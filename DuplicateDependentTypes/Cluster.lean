import DuplicateDependentTypes.Encode
import DuplicateDependentTypes.Normalize
import DuplicateDependentTypes.Match

/-!
# Clustering

1. **extract** the theorems of the selected modules (no instances, private or auto-generated
   declarations), universe parameters renamed positionally;
2. **encode and normalise** in `jobs` tasks, each on its own atom table, then name the universe
   parameters canonically (re-encoding if a name changes). The bucket key and the signature are
   computed with every atom replaced by the hash of its `Expr`, so they agree across tasks; the
   normal form itself is dropped;
3. **bucket** by key, compute the normal forms of the statements that share a bucket again on
   the merged atom table, and **match** each bucket against its class representatives (same
   signature first), buckets in tasks.
-/

namespace DuplicateDependentTypes

open Lean Meta

/-! Budgets per statement: initial graph size, `Expr` tree size, rule applications, normal form
size, heartbeats for encoding, attempts of the isomorphism search. -/
def maxSize : Nat := 3000
def maxExprSize : Nat := 20000
def maxSteps : Nat := 20000
def maxNfSize : Nat := 30000
def declHeartbeats : Nat := 50000 * 1000
def searchBudget : Nat := 100000

structure Decl where
  name : Lean.Name
  module : Lean.Name
  levelParams : List Lean.Name
  type : Expr
  deriving Inhabited

/-! ## Loading and extraction -/

private def modDir (base : System.FilePath) : Lean.Name → System.FilePath
  | .str p h => modDir base p / h
  | _ => base

private partial def oleanModulesIn (dir : System.FilePath) (pre : Lean.Name) (acc : Array Lean.Name) :
    IO (Array Lean.Name) := do
  let mut acc := acc
  for entry in ← dir.readDir do
    if ← entry.path.isDir then
      acc ← oleanModulesIn entry.path (pre ++ .mkSimple entry.fileName) acc
    else if entry.path.extension == some "olean" then
      acc := acc.push (pre ++ .mkSimple (entry.path.fileStem.getD ""))
  return acc

/-- The modules to import for a prefix: its own `.olean` if there is one, otherwise every module
below it on the search path, sorted (the order fixes the extraction order). -/
def modulesFor (p : Lean.Name) : IO (Array Lean.Name) := do
  let sp ← searchPathRef.get
  for dir in sp do
    if ← (modToFilePath dir p "olean").pathExists then return #[p]
  let mut out := #[]
  for dir in sp do
    let sub := modDir dir p
    if ← sub.isDir then out ← oleanModulesIn sub p out
  return out.qsort Lean.Name.lt

unsafe def importEnv (mods : Array Lean.Name) : IO Environment := do
  enableInitializersExecution
  importModules (mods.map ({ module := · })) {} (trustLevel := 1024) (leakEnv := true) (loadExts := true)

def isAuxiliary (n : Lean.Name) : CoreM Bool := do
  let env ← getEnv
  if ← isAutoDeclOrPrivate_Internal n then return true
  if isAuxRecursor env n || isNoConfusion env n || isRecCore env n || Meta.isMatcherCore env n then
    return true
  if n.isInternalDetail then
    if let .str _ s := n then
      if !s.startsWith "eq_" then return true
  return false

private def selectedBy (ps : Std.HashSet Lean.Name) : Lean.Name → Bool
  | .anonymous => false
  | n@(.str p _) | n@(.num p _) => ps.contains n || selectedBy ps p

def canonLevels (n : Nat) : List Lean.Name := (List.range n).map (canonLevelName ·)

/-- The theorems of the modules below `prefixes`, in module then name order. -/
def extract (prefixes : Array Lean.Name) : CoreM (Array Decl) := do
  let env ← getEnv
  let ps : Std.HashSet Lean.Name := prefixes.foldl (·.insert ·) {}
  let names := env.header.moduleNames
  let mut out := #[]
  for idx in [:names.size] do
    let m := names[idx]!
    unless selectedBy ps m do continue
    let cs := env.header.moduleData[idx]!.constants.qsort fun a b => Lean.Name.lt a.name b.name
    for c in cs do
      let n := c.name
      unless c matches .thmInfo _ do continue
      if (env.getModuleIdxFor? n).map (·.toNat) != some idx || isPrivateName n then continue
      if (← isAuxiliary n) || Meta.isInstanceCore env n then continue
      let lps := canonLevels c.levelParams.length
      let type := c.type.instantiateLevelParams c.levelParams (lps.map Level.param)
      out := out.push { name := n, module := m, levelParams := lps, type }
  return out

/-- Is the tree size of `e` at most `limit`? -/
def exprSizeLe (e : Expr) (limit : Nat) : Bool :=
  (go e limit).isSome
where
  go (e : Expr) (fuel : Nat) : Option Nat := do
    if fuel == 0 then none
    let fuel := fuel - 1
    match e with
    | .app f a => go a (← go f fuel)
    | .lam _ t b _ | .forallE _ t b _ => go b (← go t fuel)
    | .letE _ t v b _ => go b (← go v (← go t fuel))
    | .mdata _ b | .proj _ _ b => go b fuel
    | _ => some fuel

/-! ## Guards and tasks -/

/-- `x` under a fresh raw heartbeat budget, every exception turned into `.error`. -/
def guarded (raw : Nat) (x : MetaM α) : MetaM (Except String α) :=
  tryCatchRuntimeEx (do
      let start ← IO.getNumHeartbeats
      let budget (c : Core.Context) : Core.Context :=
        { c with maxHeartbeats := raw, initHeartbeats := start, options := maxHeartbeats.set c.options (raw / 1000) }
      return .ok (← withTheReader Core.Context budget x))
    fun e => return .error (← try e.toMessageData.toString catch _ => pure "error")

/-- Run the actions as dedicated tasks on copies of the current state. -/
def spawnAll (acts : Array (MetaM α)) : MetaM (Array α) := do
  let coreCtx ← readThe Core.Context
  let coreSt ← getThe Core.State
  let metaCtx ← readThe Meta.Context
  let metaSt := { (← getThe Meta.State) with cache := {} }
  let tasks ← acts.mapM fun act => IO.asTask (prio := .dedicated) do
    return (← act.toIO coreCtx coreSt metaCtx metaSt).1
  tasks.mapM fun t => do
    match ← IO.wait t with
    | .ok r => pure r
    | .error e => throwError "a task failed: {e}"

/-- Interleaved shares of `0, …, n-1`: block `b` of `blockSize` goes to share `b % jobs`. -/
def shares (n jobs blockSize : Nat) : Array (Array Nat) := Id.run do
  let mut s : Array (Array Nat) := .replicate (max 1 jobs) #[]
  for i in [:n] do
    s := s.modify (i / blockSize % max 1 jobs) (·.push i)
  return s

/-! ## Encoding and normalising -/

def encodeNormalize (table : AtomTable) (type : Expr) : MetaM (Option (Graph × AtomTable)) := do
  let r ← guarded declHeartbeats ((encodeProp maxSize type).run table)
  modify fun s => { s with cache := {} }
  let .ok (tm, table) := r | return none
  match normalize tm maxSteps maxNfSize with
  | .ok nf => return some (nf, table)
  | .error _ => return none

structure Entry where
  decl : Decl
  key : Nat
  sig : UInt64
  nfSize : Nat
  deriving Inhabited

/-- One task's share: the entries (with their declaration index) and the task's atom table. -/
def runShare (decls : Array Decl) (idxs : Array Nat) : MetaM (Array (Nat × Entry) × AtomTable) := do
  let mut table : AtomTable := {}
  let mut out := #[]
  for i in idxs do
    let d := decls[i]!
    unless exprSizeLe d.type maxExprSize do continue
    let some (nf, table') ← encodeNormalize table d.type | continue
    let ren := canonLevelRenaming d.type table'.atoms nf d.levelParams
    let mut d := { d with levelParams := ren.map (·.2) }
    let mut nf := nf
    table := table'
    unless isIdRenaming ren do
      let d' := { d with type := renameLevels d.type ren }
      if let some (nf', table') ← encodeNormalize table d'.type then
        d := d'; nf := nf'; table := table'
    let atoms := table.atoms
    let keyed := Graph.mapAtoms (fun k => (hash atoms[k]!).toNat) nf
    out := out.push (i, { decl := d, key := keyed.shapeSig, sig := (HGraph.ofGraph keyed).sig,
                          nfSize := Graph.size nf })
  return (out, table)

/-- The normal form of an entry again, on the merged atom table. -/
def renormalize (table : AtomTable) (e : Entry) : MetaM HGraph := do
  match ← encodeNormalize table e.decl.type with
  | some (nf, table') =>
    unless table'.atoms.size == table.atoms.size && Graph.size nf == e.nfSize do
      throwError "the normal form of {e.decl.name} changed"
    return HGraph.ofGraph nf
  | none => throwError "the normal form of {e.decl.name} could not be computed again"

/-! ## Classes -/

/-- The statements of a bucket as classes of isomorphic normal forms, as lists of entry indices
(the representative first). -/
def matchBucket (hgs : Std.HashMap Nat HGraph) (entries : Array Entry) (b : Array Nat) :
    Array (Array Nat) := Id.run do
  let mut cls : Array (Array Nat) := #[]
  for k in b do
    let sig := entries[k]!.sig
    let cands := (List.range cls.size).filter (entries[cls[·]![0]!]!.sig == sig) ++
      (List.range cls.size).filter (entries[cls[·]![0]!]!.sig != sig)
    match cands.find? fun ci => iso hgs[cls[ci]![0]!]! hgs[k]! searchBudget with
    | some ci => cls := cls.modify ci (·.push k)
    | none => cls := cls.push #[k]
  return cls

structure Clustering where
  extracted : Nat
  analysed : Nat
  /-- The classes with at least two members. -/
  classes : Array (Array Decl)

def cluster (prefixes : Array Lean.Name) (jobs : Nat) : MetaM Clustering := do
  let decls ← extract prefixes
  IO.eprintln s!"duplicates: {decls.size} theorems, encoding and normalising in {jobs} task(s)"
  let outs ← spawnAll ((shares decls.size jobs 64).map (runShare decls))
  let mut atoms : Array Expr := #[]
  let mut index : Std.HashMap Expr Nat := {}
  for (_, t) in outs do
    for e in t.atoms do
      unless index.contains e do
        index := index.insert e atoms.size
        atoms := atoms.push e
  let table : AtomTable := { atoms, index }
  let mut slot : Array (Option Entry) := .replicate decls.size none
  for (rs, _) in outs do
    for (i, e) in rs do slot := slot.set! i (some e)
  let entries := slot.filterMap id
  IO.eprintln s!"duplicates: {entries.size} statements normalised"
  let mut buckets : Std.HashMap Nat (Array Nat) := {}
  let mut order : Array Nat := #[]
  for h : k in [:entries.size] do
    let key := entries[k].key
    match buckets[key]? with
    | some b => buckets := buckets.insert key (b.push k)
    | none => buckets := buckets.insert key #[k]; order := order.push key
  let shared := order.filterMap fun key => let b := buckets[key]!; if b.size ≥ 2 then some b else none
  let flat := shared.flatten
  let renorm ← spawnAll ((shares flat.size jobs 16).map fun idxs =>
    idxs.mapM fun j => return (flat[j]!, ← renormalize table entries[flat[j]!]!))
  let hgs : Std.HashMap Nat HGraph := renorm.foldl (·.insertMany ·) {}
  IO.eprintln s!"duplicates: {flat.size} statements share a bucket, matching"
  let matched ← spawnAll ((shares shared.size jobs 1).map fun idxs =>
    return idxs.map fun bi => (bi, matchBucket hgs entries shared[bi]!))
  let mut perBucket : Array (Array (Array Nat)) := .replicate shared.size #[]
  for rs in matched do
    for (bi, cls) in rs do perBucket := perBucket.set! bi cls
  let classes := perBucket.flatten.filter (·.size ≥ 2) |>.map (·.map (entries[·]!.decl))
  IO.eprintln s!"duplicates: {entries.size} statements analysed, {classes.size} classes with ≥ 2 members"
  return { extracted := decls.size, analysed := entries.size, classes }

end DuplicateDependentTypes
