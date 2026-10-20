import Lean
import DuplicateDependentTypes.Graph

/-!
# Frontend: `Lean.Expr → Tm`

`encodeProp e` takes a closed proposition and returns its label. Only definitional steps are
applied: `mdata`, `let` and head β everywhere; at *proposition positions* (the root, the body of a
Prop-valued `∀`, Prop domains, the sides of `∧`/`∨`/`↔`, the body of an `∃`) `whnf` at instance
transparency, `¬a ↦ a → False` and `a ≠ b ↦ a = b → False`; the predicate of an `∃` is opened as a
binder. `∀` with a Prop body ↦ `pi`, other Π ↦ `tpi`, `∃`/`∧` ↦ `sigma`, `∨`/`↔` ↦ `conn`, `=` ↦
`eq`, `True` ↦ `unit`. Every closed compound subterm with another head, every constant (with its
levels), sort and literal is one `atom` of the run's atom table.
-/

namespace DuplicateDependentTypes

open Lean Meta

/-- The run-wide table of opaque closed terms. -/
structure AtomTable where
  atoms : Array Expr := #[]
  index : Std.HashMap Expr Nat := {}
  deriving Inhabited

abbrev EncM := StateRefT AtomTable MetaM

/-- Every level of `e` with universe parameters (in `Sort`s and constants) in Lean's normal form
(`Level.normalize`: the same universe; the arguments of `max` sorted — by parameter *name*). -/
def normalizeLevels (e : Expr) : Expr :=
  if !e.hasLevelParam then e else
  e.replace fun
    | .sort l => some (.sort l.normalize)
    | .const n ls => some (.const n (ls.map Level.normalize))
    | _ => none

/-- The index of `e` in the atom table, adding it if new. Atoms are stored with their levels
normalised (`normalizeLevels`): the same universe written two ways (`max v w` / `max w v`, as
the elaborator and a later renaming of the parameters produce) is one atom. -/
def internAtom (e : Expr) : EncM Nat := do
  let e := normalizeLevels e
  if let some k := (← get).index[e]? then return k
  modifyGet fun ⟨atoms, index⟩ =>
    let k := atoms.size
    (k, { atoms := atoms.push e, index := index.insert e k })

/-- The prefix of the error thrown when the size budget is exceeded. -/
def budgetExceededMsg : String := "encodeProp: size budget exceeded"

namespace Encode

/-- The binders entered so far. -/
structure Ctx where
  /-- Maximal `Tm.size` of the result and of every subterm. -/
  budget : Nat
  /-- Local fvar of an entered binder ↦ its binder depth (number of binders outside it). -/
  levels : Std.HashMap FVarId Nat := {}
  /-- Number of entered binders (including the anonymous binders of `∧`). -/
  depth : Nat := 0

/-- Per-call cache: (expression, proposition position?, depth) ↦ (encoding, `Tm.size`). The
fvars in the key are unique, and each has a fixed depth, so the entry is valid wherever the
same expression occurs at the same depth. -/
abbrev Cache := Std.HashMap (Expr × Bool × Nat) (Tm × Nat)

abbrev M := ReaderT Ctx (StateRefT Cache EncM)

/-- Build a node of the given size, enforcing the budget. -/
@[inline] def node (t : Tm) (size : Nat) : M (Tm × Nat) := do
  let b := (← read).budget
  if size > b then throwError "{budgetExceededMsg} ({size} > {b})"
  return (t, size)

def atomOf (e : Expr) : M (Tm × Nat) := return (.atom (← internAtom e), 1)

/-- Enter a binder `x : ty`. -/
@[inline] def withBinder (n : Lean.Name) (bi : BinderInfo) (ty : Expr) (k : Expr → M α) : M α :=
  withLocalDecl n bi ty fun x =>
    withReader (fun c => { c with levels := c.levels.insert x.fvarId! c.depth,
                                  depth := c.depth + 1 }) (k x)

/-- Enter an anonymous binder that the body does not mention (the right side of `∧`). -/
@[inline] def withDummy (k : M α) : M α :=
  withReader (fun c => { c with depth := c.depth + 1 }) k

/-- `isProp`, reading failures as "no" (the binder then stays an opaque `tpi`). -/
def isPropSafe (e : Expr) : MetaM Bool := do
  try isProp e catch _ => pure false

/-- Everywhere: strip `mdata`, ζ-reduce `let`, β-reduce the head. -/
partial def cleanTerm (e : Expr) : Expr :=
  match e with
  | .mdata _ b => cleanTerm b
  | .letE _ _ v b _ => cleanTerm (b.instantiate1 v)
  | .app .. =>
    match e.getAppFn with
    | f@(.mdata ..) | f@(.letE ..) | f@(.lam ..) =>
      let f' := cleanTerm f
      if f'.isLambda then cleanTerm (f'.betaRev e.getAppRevArgs) else mkAppN f' e.getAppArgs
    | _ => e
  | _ => e

/-- At a proposition position: `whnf` at `.instances` transparency (so that instances,
which are `[instance_reducible]` and not `[reducible]`, unfold), then `Not a ↦ a → False`,
`Ne a b ↦ a = b → False`. -/
def whnfProp (e : Expr) : MetaM Expr := do
  let e ← withReducibleAndInstances (whnf e)
  match e with
  | .app (.const ``Not []) a => return .forallE `a a (mkConst ``False) .default
  | .app (.app (.app (.const ``Ne [u]) α) a) b =>
    return .forallE `a (mkApp3 (mkConst ``Eq [u]) α a b) (mkConst ``False) .default
  | _ => return e

/-- ι: field `i` of `s` when `s` is literally a constructor application of the structure `S`. -/
def ctorField? (env : Environment) (S : Lean.Name) (i : Nat) (s : Expr) : Option Expr :=
  let s := cleanTerm s
  match s.getAppFn with
  | .const c _ => match env.find? c with
    | some (.ctorInfo ci) =>
      if ci.induct == S && i < ci.numFields && s.getAppNumArgs == ci.numParams + ci.numFields then
        some (s.getArg! (ci.numParams + i))
      else none
    | _ => none
  | _ => none

/-- Heads that are mapped to a former of `Tm` (never atomized). -/
def isFormer (e : Expr) : Bool :=
  match e with
  | .forallE .. => true
  | .proj S _ _ => S == ``And
  | .app .. =>
    match e.getAppFn with
    | .const n _ =>
      let k := e.getAppNumArgs
      ((n == ``And || n == ``Or || n == ``Iff || n == ``Exists) && k == 2) ||
      (n == ``Eq && k == 3) ||
      ((n == ``And.intro || n == ``Exists.intro) && k == 4) ||
      ((n == ``And.left || n == ``And.right) && k ≥ 3)
    | _ => false
  | _ => false

def isCompound : Expr → Bool
  | .app .. | .lam .. | .forallE .. | .proj .. => true
  | _ => false

/-- `π₁`/`π₂` with ι-reduction on a literal pair. -/
def mkProjN (b : Bool) (t : Tm × Nat) : M (Tm × Nat) :=
  match b, t.1 with
  | false, .pair _ a _ => return (a, a.size)
  | true, .pair _ _ c => return (c, c.size)
  | _, _ => node (.proj b t.1) (t.2 + 1)

/-- `s.i` (`Expr.proj S i s`, not reducible by ι) as an application `f args` that is
definitionally equal: the projection function of a structure, else a closed λ over the
parameters (it becomes an atom). -/
def projApp (S : Lean.Name) (i : Nat) (s : Expr) : MetaM (Expr × Array Expr) := do
  let env ← getEnv
  let msg := m!"encodeProp: unsupported projection {Expr.proj S i s}"
  if isStructure env S then
    if let some fld := (getStructureFields env S)[i]? then
      if let some pe ← observing? (mkProjection s fld) then
        if pe.isApp then return (pe.getAppFn, pe.getAppArgs)
  let ty ← whnf (← inferType s)
  let .const S' us := ty.getAppFn | throwError msg
  unless S' == S do throwError msg
  let ind ← getConstInfoInduct S
  let params := ty.getAppArgs.extract 0 ind.numParams
  unless params.size == ind.numParams do throwError msg
  let fn ← forallBoundedTelescope (← instantiateTypeLevelParams ind.toConstantVal us)
      ind.numParams fun ps _ =>
    withLocalDeclD `self (mkAppN (mkConst S us) ps) fun x =>
      mkLambdaFVars (ps.push x) (.proj S i x)
  if fn.hasLooseBVars || fn.hasFVar then throwError msg
  return (fn, params.push s)

mutual

/-- `⌈e⌉` at the current depth; `prop`: is this a proposition position? `e` has no loose
bound variables (binders are opened with local fvars). -/
partial def enc (e : Expr) (prop : Bool) : M (Tm × Nat) := do
  let key := (e, prop, (← read).depth)
  if let some r := (← getThe Cache)[key]? then return r
  let r ← encCore e prop
  modifyThe Cache (·.insert key r)
  return r

partial def encCore (e : Expr) (prop : Bool) : M (Tm × Nat) := do
  let e ← if prop then whnfProp e else pure (cleanTerm e)
  if isCompound e && !e.hasFVar && !isFormer e then
    return ← atomOf e
  encShape e prop

/-- The mapping proper, on a term already cleaned at its head. -/
partial def encShape (e : Expr) (prop : Bool) : M (Tm × Nat) := do
  let c ← read
  match e with
  | .bvar i => throwError "encodeProp: loose bound variable {i}"
  | .mvar _ => throwError "encodeProp: metavariable {e}"
  | .fvar id => match c.levels[id]? with
    | some l => node (.bvar (c.depth - 1 - l)) 1
    | none => throwError "encodeProp: free variable {e}"
  | .sort _ | .lit _ => atomOf e
  | .const ``True [] => node .unit 1
  | .const ``True.intro [] => node .tt 1
  | .const .. => atomOf e
  | .mdata _ b => enc b prop
  | .letE _ _ v b _ => enc (b.instantiate1 v) prop
  | .lam n t b bi => do
    let t := t.cleanupAnnotations
    let A ← enc t false
    let B ← withBinder n bi t fun x => enc (b.instantiate1 x) false
    node (.lam A.1 B.1) (A.2 + B.2 + 1)
  | .forallE n t b bi => do
    let t := t.cleanupAnnotations
    let (bodyProp, B) ← withBinder n bi t fun x => do
      let body := b.instantiate1 x
      -- at a proposition position the body is a proposition
      let bp ← if prop then pure true else isPropSafe body
      return (bp, ← enc body bp)
    if bodyProp then
      let A ← enc t (← isPropSafe t)
      node (.pi A.1 B.1) (A.2 + B.2 + 1)
    else
      let A ← enc t false
      node (.tpi A.1 B.1) (A.2 + B.2 + 1)
  | .proj S i s => do
    if S == ``And && i < 2 then
      return ← mkProjN (i == 1) (← enc s false)
    if let some f := ctorField? (← getEnv) S i s then
      return ← enc f prop
    -- a structure: the projection function `@S.f params s`; otherwise the closed λ
    -- `fun params (x : S params) => x.i` applied to `params` and `s` (definitional by β)
    let (f, args) ← projApp S i s
    encApp f args
  | .app .. => do
    let f := e.getAppFn
    let args := e.getAppArgs
    if let .const n us := f then
      match n, args.size with
      | ``And, 2 => do
        let A ← enc args[0]! true
        let B ← withDummy (enc args[1]! true)
        return ← node (.sigma .and A.1 B.1) (A.2 + B.2 + 1)
      | ``Exists, 2 => return ← encExists args[0]! args[1]!
      | ``Or, 2 => return ← encConn .or args[0]! args[1]!
      | ``Iff, 2 => return ← encConn .iff args[0]! args[1]!
      | ``Eq, 3 => do
        let T ← enc args[0]! false
        let a ← enc args[1]! false
        let b ← enc args[2]! false
        return ← node (.eq T.1 a.1 b.1) (T.2 + a.2 + b.2 + 1)
      | ``And.intro, 4 =>
        return ← encPair (mkApp2 (mkConst ``And) args[0]! args[1]!) args[2]! args[3]!
      | ``Exists.intro, 4 =>
        return ← encPair (mkApp2 (mkConst ``Exists us) args[0]! args[1]!) args[2]! args[3]!
      | ``And.left, k | ``And.right, k =>
        if k ≥ 3 then
          let mut r ← mkProjN (n == ``And.right) (← enc args[2]! false)
          for a in args[3:] do
            let a' ← enc a false
            r ← node (.app r.1 a'.1) (r.2 + a'.2 + 1)
          return r
      | _, _ => pure ()
    encApp f args

/-- A generic application spine. -/
partial def encApp (f : Expr) (args : Array Expr) : M (Tm × Nat) := do
  let mut r ← enc f false
  for a in args do
    let a' ← enc a false
    r ← node (.app r.1 a'.1) (r.2 + a'.2 + 1)
  return r

/-- `∃ x : α, p x`; a non-λ predicate is η-expanded (the body `p x` is a proposition position). -/
partial def encExists (α p : Expr) : M (Tm × Nat) := do
  let A ← enc α (← isPropSafe α)
  let B ← match cleanTerm p with
    | .lam n _ b _ => withBinder n .default α fun x => enc (b.instantiate1 x) true
    | q => withBinder `x .default α fun x => enc (mkApp q x).headBeta true
  node (.sigma .ex A.1 B.1) (A.2 + B.2 + 1)

partial def encConn (k : Conn) (a b : Expr) : M (Tm × Nat) := do
  let A ← enc a true
  let B ← enc b true
  node (.conn k A.1 B.1) (A.2 + B.2 + 1)

/-- `⟨a, b⟩ : T`, `T` a proposition position. -/
partial def encPair (T a b : Expr) : M (Tm × Nat) := do
  let T' ← enc T true
  let a' ← enc a false
  let b' ← enc b false
  node (.pair T'.1 a'.1 b'.1) (T'.2 + a'.2 + b'.2 + 1)

end

end Encode

/-- Encode a closed proposition. Throws on unsupported input and when the size budget is
exceeded. -/
def encodeProp (budget : Nat) (e : Expr) : EncM Tm := do
  let e ← instantiateMVars e
  if e.hasMVar then throwError "encodeProp: metavariables in {e}"
  if e.hasFVar then throwError "encodeProp: free variables in {e}"
  if e.hasLooseBVars then throwError "encodeProp: loose bound variables in {e}"
  let ((t, _), _) ← ((Encode.enc e true).run { budget }).run {}
  return t

/-! ## Canonical names of universe parameters

Atoms keep their levels, so two statements that differ only in the names of their universe
parameters must get the same names first. Every parameter gets a name-independent *role key* (the
sorted hashes of the atoms of a first normal form that mention it, with it replaced by `★` and the
others by `∘`); the parameters are named `u_1, u_2, …` in key order, ties broken by `tie`, then
by first occurrence.
-/

open Lean

mutual
/-- The atoms of a label, added to `s`. -/
partial def Tm.atomsInto (t : Tm) (s : Std.HashSet Nat) : Std.HashSet Nat :=
  match t with
  | .atom k => s.insert k
  | .app f a | .lam f a | .tpi f a | .pi f a | .sigma _ f a | .conn _ f a =>
    a.atomsInto (f.atomsInto s)
  | .pair T a b | .eq T a b => b.atomsInto (a.atomsInto (T.atomsInto s))
  | .proj _ t => t.atomsInto s
  | .bvar _ | .fvar _ | .unit | .tt => s

/-- The atoms of a node, added to `s`. -/
partial def Node.atomsInto (n : Node) (s : Std.HashSet Nat) : Std.HashSet Nat :=
  match n with
  | .var _ A => A.atomsInto s
  | .arrow d c | .conn _ d c => Graph.atomsInto c (Graph.atomsInto d s)
  | .eqn T a b => b.atomsInto (a.atomsInto (T.atomsInto s))

/-- The atoms of a graph, added to `s`. -/
partial def Graph.atomsInto (g : Graph) (s : Std.HashSet Nat) : Std.HashSet Nat :=
  g.foldl (fun s n => n.atomsInto s) s
end

/-- The atom indices of a graph, sorted. -/
def Graph.atomIds (g : Graph) : Array Nat :=
  (g.atomsInto {}).toArray.qsort (· < ·)

/-- The universe parameters of `e`, in order of first occurrence (pre-order). -/
def levelParamsOf (e : Expr) : Array Lean.Name :=
  (collectLevelParams {} e).params

/-- The canonical name of the `i`-th parameter (from 0). -/
def canonLevelName (i : Nat) : Lean.Name := Lean.Name.mkSimple s!"u_{i + 1}"

/-- The role key of parameter `p`. -/
def levelRoleKey (atoms : Array Expr) (ids : Array Nat) (p : Lean.Name) : Array UInt64 :=
  let hs := ids.filterMap fun k =>
    let e := atoms[k]!
    if !e.hasLevelParam then none else
    let ps := (levelParamsOf e).toList
    if !ps.contains p then none else
    let marked := normalizeLevels <| e.instantiateLevelParams ps
      (ps.map fun q => Level.param (if q == p then `«★» else `«∘»))
    some marked.hash
  hs.qsort (· < ·)

/-- Lexicographic order on keys (a proper prefix first). -/
def keyLt (a b : Array UInt64) : Bool := go 0
where
  go (i : Nat) : Bool :=
    if h : i < a.size then
      if h' : i < b.size then
        if a[i] < b[i] then true else if a[i] > b[i] then false else go (i + 1)
      else false
    else i < b.size
  termination_by a.size - i

/-- The canonical renaming of the universe parameters of `type`, as `(old, new)` pairs for the
parameters occurring in `type`, in the canonical order (the `i`-th is renamed to `u_{i+1}`).
`atoms`/`nf`: the atom table and the normal form of a first encoding of `type`; `tie`: the
tie-break order. -/
def canonLevelRenaming (type : Expr) (atoms : Array Expr) (nf : Graph) (tie : List Lean.Name) :
    List (Lean.Name × Lean.Name) :=
  let used := levelParamsOf type
  if used.isEmpty then [] else
  let ids := nf.atomIds
  let pos (p : Lean.Name) : Nat := match tie.idxOf? p with
    | some i => i
    | none => tie.length + (used.toList.idxOf? p).getD 0
  let keyed := used.map fun p => (p, levelRoleKey atoms ids p, pos p)
  let lt (x y : Lean.Name × Array UInt64 × Nat) : Bool :=
    let (_, kx, ix) := x
    let (_, ky, iy) := y
    -- parameters occurring in the normal form first
    if kx.isEmpty != ky.isEmpty then !kx.isEmpty
    else if keyLt kx ky then true
    else if keyLt ky kx then false
    else ix < iy
  let sorted := keyed.qsort lt
  (sorted.toList.zipIdx).map fun ((p, _, _), i) => (p, canonLevelName i)

/-- Is the renaming the identity? -/
def isIdRenaming (r : List (Lean.Name × Lean.Name)) : Bool :=
  r.all fun (a, b) => a == b

/-- Apply a renaming of universe parameters. -/
def renameLevels (e : Expr) (r : List (Lean.Name × Lean.Name)) : Expr :=
  if isIdRenaming r then e
  else e.instantiateLevelParams (r.map (·.1)) (r.map (Level.param ·.2))

end DuplicateDependentTypes
