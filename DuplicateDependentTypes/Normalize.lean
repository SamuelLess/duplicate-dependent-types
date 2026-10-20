import DuplicateDependentTypes.Graph
import Lean.Data.PersistentArray
import Std.Data.HashMap

/-!
# The normaliser

The rewrite system takes a graph apart as far as possible:

* `x : True` goes (`x := trivial`);
* `x : Σ y : A, B` becomes `a : A, b : B[a]` (`x := ⟨a, b⟩`): conjunctions and `∃` are curried;
* an unreferenced `x : ∀ y : A, B` becomes the arrow `[a : A] ⟶ [b : B]`, an unreferenced
  `x : A ∨ B` / `A ↔ B` / `a = b` the corresponding node;
* `[] ⟶ C` becomes `C`, `Δ ⟶ []` goes, `Δ ⟶ [Δ' ⟶ C]` becomes `Δ, Δ' ⟶ C`.

The system is confluent modulo isomorphism, so any strategy reaches the same normal form up to
`Iso`. This one is a worklist whose cost per rule does not depend on the size of the labels. A
label is a **closure** `(node, env)`: a subterm of the original statement (hash-consed in an
arena) with an environment mapping its loose de Bruijn variables to member names, so opening a
binder is O(log n); the substitutions `x := ⟨a, b⟩` / `x := trivial` are entries of a replacement
table resolved lazily, along projection paths. The side condition "no label points at `x`" is a
reference count: every arena node carries the summary of its loose variables (with the projection
path above each occurrence and a multiplicity), routed through the replacement table to the live
names they stand for, and unrouted when a label is removed. Labels are forced once, at the end.
-/

namespace DuplicateDependentTypes.Normalize

open Lean (PersistentArray)

/-- Sentinel for "no item / no product". -/
def nil : Nat := 1 <<< 60

/-! ## The arena of subterms -/

/-- Node kinds (the constructors of `Tm`). -/
inductive K where
  | bvar (i : Nat) | fvar (x : Var) | atom (k : Nat) | app | lam | tpi | unit | tt | pi
  | sigma (k : SigKind) | pair | proj (k : Bool) | conn (k : Conn) | eq
  deriving Inhabited, BEq, Hashable

/-- An occurrence group of a subterm: loose variable `bvar`, under the projection path `path`
(inner projection first), `mult` times. -/
structure Occ where
  bvar : Nat
  path : List Bool
  mult : Nat
  deriving Inhabited, Repr

def pathLt : List Bool → List Bool → Bool
  | [], [] => false
  | [], _ => true
  | _, [] => false
  | a :: as, b :: bs => (!a && b) || (a == b && pathLt as bs)

@[inline] def Occ.keyLt (a b : Occ) : Bool :=
  a.bvar < b.bvar || (a.bvar == b.bvar && pathLt a.path b.path)

@[inline] def Occ.keyEq (a b : Occ) : Bool := a.bvar == b.bvar && a.path == b.path

/-- Merge two summaries (sorted by key), adding multiplicities. -/
def mergeOcc (a b : Array Occ) : Array Occ := Id.run do
  if a.isEmpty then return b
  if b.isEmpty then return a
  let mut out : Array Occ := Array.mkEmpty (a.size + b.size)
  let mut i := 0
  let mut j := 0
  while i < a.size || j < b.size do
    if j ≥ b.size || (i < a.size && a[i]!.keyLt b[j]!) then
      out := out.push a[i]!; i := i + 1
    else if i ≥ a.size || b[j]!.keyLt a[i]! then
      out := out.push b[j]!; j := j + 1
    else
      out := out.push { a[i]! with mult := a[i]!.mult + b[j]!.mult }; i := i + 1; j := j + 1
  return out

/-- The summary of a body under one binder: variable 0 is bound, the others shift down. -/
def shiftOcc (a : Array Occ) : Array Occ :=
  a.filterMap fun o => if o.bvar == 0 then none else some { o with bvar := o.bvar - 1 }

structure ANode where
  k : K
  kids : Array Nat
  /-- The subterm itself (forcing rebuilds from it). -/
  tm : Tm
  occ : Array Occ
  /-- `(i, path)` if the node is a chain of projections over the loose variable `i` (or that
  variable itself). -/
  chain : Option (Nat × List Bool)
  deriving Inhabited

/-- The arena: hash-consed subterms of one statement. -/
structure Arena where
  nodes : Array ANode := #[]
  index : Std.HashMap (K × Array Nat) Nat := {}
  deriving Inhabited

namespace Arena

def intern (a : Arena) (k : K) (kids : Array Nat) (tm : Tm) (occ : Array Occ)
    (chain : Option (Nat × List Bool)) : Nat × Arena :=
  match a.index[(k, kids)]? with
  | some i => (i, a)
  | none =>
    let i := a.nodes.size
    (i, { nodes := a.nodes.push { k, kids, tm, occ, chain }, index := a.index.insert (k, kids) i })

/-- Add a term and all its subterms; returns the node of the term. Subterms are memoised by
object identity (`ptrAddrUnsafe`: the encoder shares equal subterms as objects, and the input
term stays alive during the traversal, so addresses are stable) and then hash-consed
structurally. -/
unsafe def addUnsafe (a : Arena) (memo : Std.HashMap USize Nat) (t : Tm) :
    Nat × Arena × Std.HashMap USize Nat :=
  let key := ptrAddrUnsafe t
  match memo[key]? with
  | some i => (i, a, memo)
  | none =>
    let (i, a, memo) := go a memo t
    (i, a, memo.insert key i)
where
  go (a : Arena) (memo : Std.HashMap USize Nat) (t : Tm) : Nat × Arena × Std.HashMap USize Nat :=
    match t with
    | .bvar i => let (i, a) := a.intern (.bvar i) #[] t #[⟨i, [], 1⟩] (some (i, [])); (i, a, memo)
    | .fvar x => let (i, a) := a.intern (.fvar x) #[] t #[] none; (i, a, memo)
    | .atom k => let (i, a) := a.intern (.atom k) #[] t #[] none; (i, a, memo)
    | .unit => let (i, a) := a.intern .unit #[] t #[] none; (i, a, memo)
    | .tt => let (i, a) := a.intern .tt #[] t #[] none; (i, a, memo)
    | .app f x => bin a memo .app f x t false
    | .conn k f x => bin a memo (.conn k) f x t false
    | .lam A b => bin a memo .lam A b t true
    | .tpi A b => bin a memo .tpi A b t true
    | .pi A b => bin a memo .pi A b t true
    | .sigma k A b => bin a memo (.sigma k) A b t true
    | .pair T x y => tern a memo .pair T x y t
    | .eq T x y => tern a memo .eq T x y t
    | .proj k u =>
      let (iu, a, memo) := addUnsafe a memo u
      let nu := a.nodes[iu]!
      match nu.chain with
      | some (i, p) =>
        let (i', a) := a.intern (.proj k) #[iu] t #[⟨i, p ++ [k], 1⟩] (some (i, p ++ [k])); (i', a, memo)
      | none => let (i', a) := a.intern (.proj k) #[iu] t nu.occ none; (i', a, memo)
  bin (a : Arena) (memo : Std.HashMap USize Nat) (k : K) (x y : Tm) (t : Tm) (binder : Bool) :
      Nat × Arena × Std.HashMap USize Nat :=
    let (ix, a, memo) := addUnsafe a memo x
    let (iy, a, memo) := addUnsafe a memo y
    let oy := a.nodes[iy]!.occ
    let occ := mergeOcc a.nodes[ix]!.occ (if binder then shiftOcc oy else oy)
    let (i, a) := a.intern k #[ix, iy] t occ none
    (i, a, memo)
  tern (a : Arena) (memo : Std.HashMap USize Nat) (k : K) (x y z : Tm) (t : Tm) :
      Nat × Arena × Std.HashMap USize Nat :=
    let (ix, a, memo) := addUnsafe a memo x
    let (iy, a, memo) := addUnsafe a memo y
    let (iz, a, memo) := addUnsafe a memo z
    let occ := mergeOcc (mergeOcc a.nodes[ix]!.occ a.nodes[iy]!.occ) a.nodes[iz]!.occ
    let (i, a) := a.intern k #[ix, iy, iz] t occ none
    (i, a, memo)

@[implemented_by addUnsafe]
opaque addImpl (a : Arena) (memo : Std.HashMap USize Nat) (t : Tm) :
    Nat × Arena × Std.HashMap USize Nat

/-- Add a term and all its subterms; returns the node of the term. -/
def add (a : Arena) (t : Tm) : Nat × Arena :=
  let (i, a, _) := addImpl a {} t
  (i, a)

end Arena

/-! ## Closures, items, products -/

abbrev Env := PersistentArray Var

/-- A label: a subterm with an environment for its loose variables (`bvar i ↦ env[size-1-i]`). -/
structure Clo where
  node : Nat
  env : Env
  deriving Inhabited

@[inline] def Env.lookup (env : Env) (i : Nat) : Var := env.get! (env.size - 1 - i)

inductive ItemK where
  | var (x : Var) (A : Clo)
  | arrow (dom cod : Nat)
  | conn (k : Conn) (a b : Nat)
  /-- The `eq` label as a whole (its three parts share the environment). -/
  | eqn (c : Clo)
  | dead
  deriving Inhabited

structure Item where
  k : ItemK
  prod : Nat
  prev : Nat := nil
  next : Nat := nil
  deriving Inhabited

structure Prod where
  head : Nat := nil
  tail : Nat := nil
  count : Nat := 0
  parent : Nat := nil
  deriving Inhabited

/-- What became of a member. -/
inductive Repl where
  | live
  | tt
  | pair (T : Clo) (a b : Var)
  deriving Inhabited

structure St where
  arena : Arena := {}
  items : Array Item := #[]
  prods : Array Prod := #[]
  repl : Array Repl := #[]
  /-- Routed demands per live name. -/
  cnt : Array Nat := #[]
  demands : Array (Std.HashMap (List Bool) Nat) := #[]
  itemOfName : Array Nat := #[]
  fresh : Nat := 0
  work : Array Nat := #[]
  steps : Nat := 0
  deriving Inhabited

abbrev M := StateM St

@[inline] def getItem (i : Nat) : M Item := return (← get).items[i]!
@[inline] def setItem (i : Nat) (v : Item) : M Unit := modify fun s =>
  let a := s.items; let s := { s with items := #[] }; { s with items := a.set! i v }
@[inline] def modifyItem (i : Nat) (f : Item → Item) : M Unit := modify fun s =>
  let a := s.items; let s := { s with items := #[] }; { s with items := a.modify i f }
@[inline] def getProd (p : Nat) : M Prod := return (← get).prods[p]!
@[inline] def modifyProd (p : Nat) (f : Prod → Prod) : M Unit := modify fun s =>
  let a := s.prods; let s := { s with prods := #[] }; { s with prods := a.modify p f }
@[inline] def pushWork (i : Nat) : M Unit := modify fun s =>
  let a := s.work; let s := { s with work := #[] }; { s with work := a.push i }
@[inline] def node (i : Nat) : M ANode := return (← get).arena.nodes[i]!

def newProd (parent : Nat) : M Nat := modifyGet fun s =>
  let a := s.prods; let s := { s with prods := #[] }
  (a.size, { s with prods := a.push { parent } })

def newItem (k : ItemK) (prod : Nat) : M Nat := modifyGet fun s =>
  let a := s.items; let s := { s with items := #[] }
  (a.size, { s with items := a.push { k, prod } })

def freshName (item : Nat) : M Var := modifyGet fun s =>
  let x := s.fresh
  let r := s.repl; let c := s.cnt; let d := s.demands; let io := s.itemOfName
  let s := { s with repl := #[], cnt := #[], demands := #[], itemOfName := #[] }
  (x, { s with fresh := x + 1, repl := r.push .live, cnt := c.push 0, demands := d.push {},
                itemOfName := io.push item })

def forgetName (x : Var) : M Unit := modify fun s =>
  let io := s.itemOfName; let s := { s with itemOfName := #[] }
  { s with itemOfName := io.set! x nil }

/-! ## Routing of occurrences -/

/-- A member's rule may apply once nothing points at it. -/
def isCountRule : K → Bool
  | .pi | .conn _ | .eq => true
  | _ => false

mutual
/-- Route `m` occurrences of name `g` under `path` to the live names they stand for. -/
partial def route (g : Var) (path : List Bool) (m : Nat) : M Unit := do
  match (← get).repl[g]! with
  | .live => modify fun s =>
      let c := s.cnt; let d := s.demands
      let s := { s with cnt := #[], demands := #[] }
      { s with cnt := c.modify g (· + m),
               demands := d.modify g fun dm => dm.insert path (dm.getD path 0 + m) }
  | .tt => pure ()
  | .pair T a b =>
    match path with
    | [] => routeClo T m; route a [] m; route b [] m
    | k :: q => route (if k then b else a) q m
/-- Route every occurrence of a label. -/
partial def routeClo (c : Clo) (m : Nat) : M Unit := do
  for o in (← node c.node).occ do
    route (c.env.lookup o.bvar) o.path (o.mult * m)
end

mutual
/-- Undo `route`; a live name whose count reaches 0 is rechecked. -/
partial def unroute (g : Var) (path : List Bool) (m : Nat) : M Unit := do
  match (← get).repl[g]! with
  | .live =>
    let zero ← modifyGet fun s =>
      let c := s.cnt; let d := s.demands
      let s := { s with cnt := #[], demands := #[] }
      let n := c[g]! - m
      (n == 0, { s with cnt := c.set! g n,
                        demands := d.modify g fun dm =>
                          let v := dm.getD path 0
                          if v ≤ m then dm.erase path else dm.insert path (v - m) })
    if zero then
      let it := (← get).itemOfName[g]!
      if it != nil then pushWork it
  | .tt => pure ()
  | .pair T a b =>
    match path with
    | [] => unrouteClo T m; unroute a [] m; unroute b [] m
    | k :: q => unroute (if k then b else a) q m
partial def unrouteClo (c : Clo) (m : Nat) : M Unit := do
  for o in (← node c.node).occ do
    unroute (c.env.lookup o.bvar) o.path (o.mult * m)
end

/-- Replace `h` (taking its demands away first) and forward them through the new entry. -/
def replace (h : Var) (r : Repl) : M Unit := do
  let dm ← modifyGet fun s =>
    let d := s.demands; let rp := s.repl
    let s := { s with demands := #[], repl := #[] }
    (d[h]!, { s with demands := d.set! h {}, repl := rp.set! h r })
  for (p, m) in dm do
    route h p m

/-! ## Linking -/

def appendItem (p i : Nat) : M Unit := do
  let pr ← getProd p
  modifyItem i fun it => { it with prod := p, prev := pr.tail, next := nil }
  if pr.tail != nil then modifyItem pr.tail fun it => { it with next := i }
  modifyProd p fun pr => { pr with head := if pr.head == nil then i else pr.head, tail := i,
                                   count := pr.count + 1 }

def insertAfter (a i : Nat) : M Unit := do
  let ia ← getItem a
  let p := ia.prod
  modifyItem i fun it => { it with prod := p, prev := a, next := ia.next }
  if ia.next != nil then modifyItem ia.next fun it => { it with prev := i }
  modifyItem a fun it => { it with next := i }
  modifyProd p fun pr => { pr with tail := if pr.tail == a then i else pr.tail, count := pr.count + 1 }

def unlink (i : Nat) : M Unit := do
  let it ← getItem i
  if it.prev != nil then modifyItem it.prev fun x => { x with next := it.next }
  if it.next != nil then modifyItem it.next fun x => { x with prev := it.prev }
  modifyProd it.prod fun pr =>
    { pr with head := if pr.head == i then it.next else pr.head,
              tail := if pr.tail == i then it.prev else pr.tail, count := pr.count - 1 }

partial def itemsOf (p : Nat) : M (Array Nat) := do
  let pr ← getProd p
  let mut out := #[]
  let mut cur := pr.head
  while cur != nil do
    out := out.push cur
    cur := (← getItem cur).next
  return out

/-! ## Rules -/

partial def killItem (i : Nat) : M Unit := do
  let it ← getItem i
  match it.k with
  | .var x A => unrouteClo A 1; forgetName x
  | .eqn c => unrouteClo c 1
  | .arrow d c => killProdItems d; killProdItems c
  | .conn _ a b => killProdItems a; killProdItems b
  | .dead => pure ()
  setItem i { it with k := .dead }
where
  killProdItems (p : Nat) : M Unit := do
    for j in ← itemsOf p do killItem j

def recheckParent (p : Nat) : M Unit := do
  let pr ← getProd p
  if pr.parent != nil then pushWork pr.parent

def bumpSteps : M Unit := modify fun s => { s with steps := s.steps + 1 }

/-- A new member `x : (kid, env)` of product `p` (not linked yet). -/
def mkMember (p : Nat) (kid : Nat) (env : Env) : M (Nat × Var) := do
  let j ← newItem .dead p
  let x ← freshName j
  let c : Clo := { node := kid, env }
  setItem j { k := .var x c, prod := p }
  routeClo c 1
  return (j, x)

/-- `x : True` goes, `x := trivial`. -/
def ruleUnit (i : Nat) (x : Var) : M Unit := do
  bumpSteps
  let p := (← getItem i).prod
  replace x .tt
  unlink i
  killItem i
  recheckParent p

/-- `x : Σ y : A, B` becomes `a : A, b : B[a]`, `x := ⟨a, b⟩`. -/
def ruleSigma (i : Nat) (x : Var) (c : Clo) : M Unit := do
  bumpSteps
  let p := (← getItem i).prod
  let n ← node c.node
  let (ja, a) ← mkMember p n.kids[0]! c.env
  let (jb, b) ← mkMember p n.kids[1]! (c.env.push a)
  insertAfter i ja
  insertAfter ja jb
  replace x (.pair c a b)
  unlink i
  killItem i
  pushWork ja; pushWork jb
  recheckParent p

/-- An unreferenced `x : ∀ y : A, B` becomes `[a : A] ⟶ [b : B[a]]`. -/
def rulePi (i : Nat) (x : Var) (c : Clo) : M Unit := do
  bumpSteps
  let it ← getItem i
  let n ← node c.node
  let pd ← newProd i
  let pc ← newProd i
  let (ja, a) ← mkMember pd n.kids[0]! c.env
  let (jb, _) ← mkMember pc n.kids[1]! (c.env.push a)
  unrouteClo c 1
  forgetName x
  appendItem pd ja
  appendItem pc jb
  setItem i { it with k := .arrow pd pc }
  pushWork ja; pushWork jb; pushWork i
  recheckParent it.prod

/-- An unreferenced `x : A ∨ B` / `A ↔ B` becomes the node `[a : A] ∨ [b : B]`. -/
def ruleConn (i : Nat) (x : Var) (k : Conn) (c : Clo) : M Unit := do
  bumpSteps
  let it ← getItem i
  let n ← node c.node
  let pa ← newProd i
  let pb ← newProd i
  let (ja, _) ← mkMember pa n.kids[0]! c.env
  let (jb, _) ← mkMember pb n.kids[1]! c.env
  unrouteClo c 1
  forgetName x
  appendItem pa ja
  appendItem pb jb
  setItem i { it with k := .conn k pa pb }
  pushWork ja; pushWork jb
  recheckParent it.prod

/-- An unreferenced `x : a = b` becomes the node `a = b` (same occurrences, nothing to route). -/
def ruleEq (i : Nat) (x : Var) (c : Clo) : M Unit := do
  bumpSteps
  let it ← getItem i
  forgetName x
  setItem i { it with k := .eqn c }
  recheckParent it.prod

def ruleArrowUnit (i : Nat) (c : Nat) : M Unit := do
  bumpSteps
  let it ← getItem i
  let p := it.prod
  let mut after := i
  for j in ← itemsOf c do
    unlink j
    insertAfter after j
    after := j
    pushWork j
  unlink i
  setItem i { it with k := .dead }
  recheckParent p

def ruleArrowErase (i : Nat) : M Unit := do
  bumpSteps
  let p := (← getItem i).prod
  unlink i
  killItem i
  recheckParent p

def ruleArrowMerge (i d : Nat) (j d' c' : Nat) : M Unit := do
  bumpSteps
  let it ← getItem i
  for x in ← itemsOf d' do
    unlink x
    appendItem d x
  modifyProd c' fun pr => { pr with parent := i }
  unlink j
  let jt ← getItem j
  setItem j { jt with k := .dead }
  setItem i { it with k := .arrow d c' }
  pushWork i

def check (i : Nat) : M Unit := do
  let it ← getItem i
  match it.k with
  | .var x c =>
    match (← node c.node).k with
    | .unit => ruleUnit i x
    | .sigma _ => ruleSigma i x c
    | .pi => if (← get).cnt[x]! == 0 then rulePi i x c
    | .conn k => if (← get).cnt[x]! == 0 then ruleConn i x k c
    | .eq => if (← get).cnt[x]! == 0 then ruleEq i x c
    | _ => pure ()
  | .arrow d c =>
    let pd ← getProd d
    let pc ← getProd c
    if pd.count == 0 then ruleArrowUnit i c
    else if pc.count == 0 then ruleArrowErase i
    else if pc.count == 1 then
      let j := pc.head
      if let .arrow d' c' := (← getItem j).k then ruleArrowMerge i d j d' c'
  | _ => pure ()

/-! ## Forcing -/

/-- `proj k₂ (proj k₁ t)` for the path `[k₁, k₂]`. -/
def wrapProj (p : List Bool) (t : Tm) : Tm := p.foldl (fun t k => .proj k t) t

/-- The chain of projections over a loose variable (`≥ d`), if `t` is one. -/
def chainTm (d : Nat) : Tm → Option (Nat × List Bool)
  | .bvar i => if i ≥ d then some (i - d, []) else none
  | .proj k u => (chainTm d u).map fun (i, p) => (i, p ++ [k])
  | _ => none

mutual
/-- The forced label: the subterm with its loose variables resolved through the environment and
the replacement table (hereditary ι along projection paths). -/
partial def forceTm (s : St) (env : Env) (d : Nat) : Tm → Tm
  | .bvar i => if i < d then .bvar i else resolve s (env.lookup (i - d)) []
  | t@(.proj k u) =>
    match chainTm d t with
    | some (i, p) => resolve s (env.lookup i) p
    -- not a projection of a pointer: never reduced, even a literal `proj k (pair …)`
    | none => .proj k (forceTm s env d u)
  | .fvar x => .fvar x
  | .atom k => .atom k
  | .unit => .unit
  | .tt => .tt
  | .app f a => .app (forceTm s env d f) (forceTm s env d a)
  | .lam A b => .lam (forceTm s env d A) (forceTm s env (d + 1) b)
  | .tpi A B => .tpi (forceTm s env d A) (forceTm s env (d + 1) B)
  | .pi A B => .pi (forceTm s env d A) (forceTm s env (d + 1) B)
  | .sigma k A B => .sigma k (forceTm s env d A) (forceTm s env (d + 1) B)
  | .pair T a b => .pair (forceTm s env d T) (forceTm s env d a) (forceTm s env d b)
  | .conn k A B => .conn k (forceTm s env d A) (forceTm s env d B)
  | .eq T a b => .eq (forceTm s env d T) (forceTm s env d a) (forceTm s env d b)
/-- What the pointer `h` under the projection path `p` stands for now. -/
partial def resolve (s : St) (h : Var) (p : List Bool) : Tm :=
  match s.repl[h]!, p with
  | .live, p => wrapProj p (.fvar h)
  | .tt, p => wrapProj p .tt
  | .pair T a b, [] => .pair (forceClo s T) (resolve s a []) (resolve s b [])
  | .pair _ a b, k :: q => resolve s (if k then b else a) q
partial def forceClo (s : St) (c : Clo) : Tm :=
  forceTm s c.env 0 s.arena.nodes[c.node]!.tm
end

/-- The normal form as a `Graph`. -/
partial def toGraph (s : St) (p : Nat) : Graph := Id.run do
  let mut out : Array Node := #[]
  let mut cur := s.prods[p]!.head
  while cur != nil do
    let it := s.items[cur]!
    match it.k with
    | .var x c => out := out.push (.var x (forceClo s c))
    | .arrow d c => out := out.push (.arrow (toGraph s d) (toGraph s c))
    | .conn k a b => out := out.push (.conn k (toGraph s a) (toGraph s b))
    | .eqn c =>
      match forceClo s c with
      | .eq T a b => out := out.push (.eqn T a b)
      | t => out := out.push (.var x_fail t)   -- unreachable: an `eq` label forces to an `eq`
    | .dead => pure ()
    cur := it.next
  return out.toList
where x_fail : Var := nil

/-! ## The loop -/

partial def loop (maxSteps : Nat) : M (Option String) := do
  let s ← get
  if s.work.isEmpty then return none
  if s.steps > maxSteps then return some "steps"
  let i := s.work.back!
  set { s with work := s.work.pop }
  check i
  loop maxSteps

end Normalize

open Normalize in
/-- The normal form of the graph `[x : t]` of a closed label `t`; `.error "steps"` /
`.error "size"` when more than `maxSteps` rules apply or the normal form is larger than
`maxSize`. -/
def normalize (t : Tm) (maxSteps maxSize : Nat) : Except String Graph :=
  let init : M (Option String) := do
    let (root, arena) := (({} : Arena).add t)
    modify fun s => { s with arena }
    let p ← newProd nil
    let (i, _) ← mkMember p root {}
    appendItem p i
    pushWork i
    loop maxSteps
  let (r, s) := init.run {}
  match r with
  | some w => .error w
  | none =>
    let g := toGraph s 0
    let size := Graph.size g
    if size > maxSize then .error "size" else .ok g

end DuplicateDependentTypes
