import DuplicateDependentTypes.Graph
import Std.Data.TreeMap
import Std.Data.HashMap
import Std.Data.HashSet

/-!
# Isomorphism of normal forms

`Iso`: bijective renaming, reordering of every product, flips of connective and equation sides.

* `Graph.shapeSig`, the bucket key: a hash of the graph blind to names, pointers, order and flips.
* `HGraph.sig`, a finer `Iso`-invariant signature: every member gets a colour (the shape of its
  label and the kinds of products it sits in), refined a few rounds Weisfeiler–Leman style by the
  colours of the members its label points at and of the members pointing at it. Products and
  sides are combined commutatively, names never enter a hash.
* `iso`, a backtracking search for the renaming: members are matched only against members of
  equal hash, fewest candidates first, referrers before the members they point at, so on typical
  inputs it never backtracks. A budget bounds the attempts (exhaustion counts as "not isomorphic").
-/

namespace DuplicateDependentTypes

/-! ## Hashing -/

namespace IsoHash

/-- SplitMix64 finaliser. -/
@[inline] def fin (h : UInt64) : UInt64 :=
  let h := (h ^^^ (h >>> 30)) * 0xbf58476d1ce4e5b9
  let h := (h ^^^ (h >>> 27)) * 0x94d049bb133111eb
  h ^^^ (h >>> 31)

/-- Ordered combination. -/
@[inline] def mix (a b : UInt64) : UInt64 := fin (a * 0x9e3779b97f4a7c15 + b + 0x632be59bd9b4e019)

/-- Unordered combination of two values. -/
@[inline] def sym (a b : UInt64) : UInt64 := mix 0x5bd1e9955bd1e995 (fin a + fin b)

/-- Colour of a pointer to a name that is not a member of the graph. -/
def freeColour : UInt64 := 0x2545f4914f6cdd1d

/-- Hash of a label, the pointers replaced by `col` of their target. -/
def tmHash (col : Var → UInt64) : Tm → UInt64
  | .bvar k => mix 1 k.toUInt64
  | .fvar i => mix 2 (col i)
  | .atom k => mix 3 k.toUInt64
  | .app f a => mix (mix 4 (tmHash col f)) (tmHash col a)
  | .lam A b => mix (mix 5 (tmHash col A)) (tmHash col b)
  | .tpi A B => mix (mix 6 (tmHash col A)) (tmHash col B)
  | .unit => 7
  | .tt => 8
  | .pi A B => mix (mix 9 (tmHash col A)) (tmHash col B)
  | .sigma k A B => mix (mix (mix 10 (if k == .ex then 0 else 1)) (tmHash col A)) (tmHash col B)
  | .pair T a b => mix (mix (mix 11 (tmHash col T)) (tmHash col a)) (tmHash col b)
  | .proj k t => mix (mix 12 (if k then 1 else 0)) (tmHash col t)
  | .conn k A B => mix (mix (mix 13 (if k == .or then 0 else 1)) (tmHash col A)) (tmHash col B)
  | .eq T a b => mix (mix (mix 14 (tmHash col T)) (tmHash col a)) (tmHash col b)

/-- The pointer occurrences of a label with the hash of their path from the root. -/
def tmOcc (p : UInt64) : Tm → List (Var × UInt64) → List (Var × UInt64)
  | .fvar i, acc => (i, p) :: acc
  | .app f a, acc => tmOcc (mix p 41) f (tmOcc (mix p 42) a acc)
  | .lam A b, acc => tmOcc (mix p 51) A (tmOcc (mix p 52) b acc)
  | .tpi A B, acc => tmOcc (mix p 61) A (tmOcc (mix p 62) B acc)
  | .pi A B, acc => tmOcc (mix p 91) A (tmOcc (mix p 92) B acc)
  | .sigma k A B, acc =>
      let p := mix p (if k == .ex then 100 else 101)
      tmOcc (mix p 1) A (tmOcc (mix p 2) B acc)
  | .pair T a b, acc => tmOcc (mix p 111) T (tmOcc (mix p 112) a (tmOcc (mix p 113) b acc))
  | .proj k t, acc => tmOcc (mix p (if k then 121 else 122)) t acc
  | .conn k A B, acc =>
      let p := mix p (if k == .or then 130 else 131)
      tmOcc (mix p 1) A (tmOcc (mix p 2) B acc)
  | .eq T a b, acc => tmOcc (mix p 141) T (tmOcc (mix p 142) a (tmOcc (mix p 143) b acc))
  | _, acc => acc

/-- Product kinds, for the context part of the initial colour (sides of a connective share a
tag, so flips do not change it). -/
def ctxDom : UInt64 := 0x1d
def ctxCod : UInt64 := 0x2d
def ctxSide : UInt64 := 0x3d

/-- The members and equation nodes of a graph, with the kind-path of their product. -/
structure Flat where
  vars : Array (Var × Tm × UInt64) := #[]
  eqns : Array (Tm × Tm × Tm × UInt64) := #[]

mutual
def flatten (ctx : UInt64) : Graph → Flat → Flat
  | [], f => f
  | n :: g, f => flatten ctx g (flattenN ctx n f)
def flattenN (ctx : UInt64) : Node → Flat → Flat
  | .var x A, f => { f with vars := f.vars.push (x, A, ctx) }
  | .arrow d c, f => flatten (mix ctx ctxCod) c (flatten (mix ctx ctxDom) d f)
  | .conn k a b, f =>
      let ctx' := mix (mix ctx ctxSide) (if k == .or then 0 else 1)
      flatten ctx' b (flatten ctx' a f)
  | .eqn T a b, f => { f with eqns := f.eqns.push (T, a, b, ctx) }
end

abbrev Colours := Std.HashMap Var UInt64

@[inline] def Colours.col (c : Colours) (x : Var) : UInt64 := c.getD x freeColour

/-- Hash of an equation node under a colouring (sides unordered). -/
@[inline] def eqnHash (col : Var → UInt64) (T a b : Tm) : UInt64 :=
  mix (mix 0xe9 (tmHash col T)) (sym (tmHash col a) (tmHash col b))

def initColours (f : Flat) : Colours :=
  f.vars.foldl (init := {}) fun c (x, A, ctx) =>
    -- duplicate names (not `WF`) are merged commutatively, so the result does not depend on the
    -- order
    c.insert x (c.getD x 0 + mix ctx (tmHash (fun _ => freeColour) A))

/-- One round of colour refinement. -/
def refine (f : Flat) (c : Colours) : Colours := Id.run do
  let col := c.col
  let mut back : Std.HashMap Var UInt64 := {}
  for (x, A, _) in f.vars do
    let rc := col x
    for (y, p) in tmOcc 0x77 A [] do
      back := back.insert y (back.getD y 0 + fin (mix rc p))
  for (T, a, b, _) in f.eqns do
    let rc := eqnHash col T a b
    for (y, p) in tmOcc 0x78 T (tmOcc 0x79 a (tmOcc 0x79 b [])) do
      back := back.insert y (back.getD y 0 + fin (mix rc p))
  let mut out : Colours := {}
  for (x, A, _) in f.vars do
    out := out.insert x (out.getD x 0 + mix (mix (col x) (tmHash col A)) (back.getD x 0))
  return out

def classes (c : Colours) : Nat :=
  (c.fold (init := ({} : Std.HashSet UInt64)) fun s _ v => s.insert v).size

/-- At most this many refinement rounds. -/
def maxRounds : Nat := 5

/-- The refined colouring of a graph. -/
def colours (g : Graph) : Colours := Id.run do
  let f := flatten 0 g {}
  let mut c := initColours f
  let mut k := classes c
  for _ in [0:maxRounds] do
    let c' := refine f c
    let k' := classes c'
    c := c'
    if k' ≤ k then break
    k := k'
  return c

end IsoHash

open IsoHash

/-- A node annotated with its `Iso`-invariant hash (and, for connectives and equations, the
hashes of the two sides). -/
inductive HNode where
  | var : UInt64 → Var → Tm → HNode
  | arrow : UInt64 → List HNode → List HNode → HNode
  | conn : UInt64 → Conn → List HNode → List HNode → UInt64 → UInt64 → HNode
  | eqn : UInt64 → Tm → Tm → Tm → UInt64 → UInt64 → HNode
  deriving Inhabited

def HNode.hash : HNode → UInt64
  | .var h .. | .arrow h .. | .conn h .. | .eqn h .. => h

/-- Hash of a product from the hashes of its members (a multiset hash). -/
def prodHash (hs : List HNode) : UInt64 :=
  mix 0xa11 (hs.foldl (fun acc n => acc + fin n.hash) 0)

mutual
def annotate (c : Colours) : Graph → List HNode
  | [] => []
  | n :: g => annotateN c n :: annotate c g
def annotateN (c : Colours) : Node → HNode
  | .var x A => .var (mix 0xb1 (c.col x)) x A
  | .arrow d e =>
      let d' := annotate c d
      let e' := annotate c e
      .arrow (mix (mix 0xb2 (prodHash d')) (prodHash e')) d' e'
  | .conn k a b =>
      let a' := annotate c a
      let b' := annotate c b
      let ha := prodHash a'
      let hb := prodHash b'
      .conn (mix (mix 0xb3 (if k == .or then 0 else 1)) (sym ha hb)) k a' b' ha hb
  | .eqn T a b =>
      let ha := tmHash c.col a
      let hb := tmHash c.col b
      .eqn (mix (mix 0xb4 (tmHash c.col T)) (sym ha hb)) T a b ha hb
end

/-- A graph prepared for matching: annotated nodes and the signature. -/
structure HGraph where
  nodes : List HNode
  sig : UInt64
  deriving Inhabited

def HGraph.ofGraph (g : Graph) : HGraph :=
  let nodes := annotate (colours g) g
  { nodes, sig := prodHash nodes }

/-! ## The search -/

/-- A partial injection on names (persistent, for backtracking). -/
structure PM where
  fwd : Std.TreeMap Var Var compare := {}
  bwd : Std.TreeMap Var Var compare := {}

namespace PM

/-- Extend by `i ↦ j`, if that keeps it a partial injection. -/
@[inline] def bind (σ : PM) (i j : Var) : Option PM :=
  match σ.fwd.get? i with
  | some j' => if j == j' then some σ else none
  | none => if σ.bwd.contains j then none else some ⟨σ.fwd.insert i j, σ.bwd.insert j i⟩

/-- Extend so that renaming `t` gives `t'`. -/
def matchTm (σ : PM) : Tm → Tm → Option PM
  | .bvar k, .bvar k' | .atom k, .atom k' => if k == k' then some σ else none
  | .fvar i, .fvar j => σ.bind i j
  | .app f a, .app f' a' | .lam f a, .lam f' a' | .tpi f a, .tpi f' a' | .pi f a, .pi f' a' =>
      (matchTm σ f f').bind (matchTm · a a')
  | .unit, .unit | .tt, .tt => some σ
  | .sigma k A B, .sigma k' A' B' =>
      if k == k' then (matchTm σ A A').bind (matchTm · B B') else none
  | .conn k A B, .conn k' A' B' =>
      if k == k' then (matchTm σ A A').bind (matchTm · B B') else none
  | .pair T a b, .pair T' a' b' | .eq T a b, .eq T' a' b' =>
      ((matchTm σ T T').bind (matchTm · a a')).bind (matchTm · b b')
  | .proj k t, .proj k' t' => if k == k' then matchTm σ t t' else none
  | _, _ => none

end PM

/-- The search monad: the state is the remaining budget, an exception means it ran out. -/
abbrev SearchM := EStateM Unit Nat

@[inline] def tick : SearchM Unit := do
  let n ← get
  if n == 0 then throw () else set (n - 1)

/-- Can source node `s` be tried against target `t` under `σ` (cheap filter)? -/
@[inline] def admissible (σ : PM) (s t : HNode) : Bool :=
  s.hash == t.hash &&
  match s, t with
  | .var _ x _, .var _ y _ => match σ.fwd.get? x with
    | some y' => y == y'
    | none => !σ.bwd.contains y
  | _, _ => true

/-- The trial order of a product's members: fewest hash-equal candidates first, then reverse
list order (referrers before the members they point at). -/
def trialOrder (src : List HNode) (tgt : Array HNode) : List HNode :=
  let keyed := src.toArray.mapIdx fun i s => (tgt.foldl (fun k t => if t.hash == s.hash then k + 1 else k) 0, i, s)
  (keyed.qsort fun (c₁, i₁, _) (c₂, i₂, _) => c₁ < c₂ || (c₁ == c₂ && i₁ > i₂)).toList.map (·.2.2)

mutual
/-- Match the members `src` (in trial order) one-to-one with the target members at indices
`free`, then continue with `k` (which may fail and make the search backtrack). -/
partial def matchMembers (σ : PM) (src : List HNode) (tgt : Array HNode) (free : List Nat)
    (k : PM → SearchM Bool) : SearchM Bool :=
  match src with
  | [] => k σ
  | s :: rest =>
    (free.filter (admissible σ s tgt[·]!)).anyM fun i => do
      tick
      matchNode σ s tgt[i]! fun σ => matchMembers σ rest tgt (free.erase i) k

partial def matchProd (σ : PM) (src tgt : List HNode) (k : PM → SearchM Bool) : SearchM Bool :=
  if src.length != tgt.length then pure false else
  let tgt := tgt.toArray
  matchMembers σ (trialOrder src tgt) tgt (List.range tgt.size) k

partial def matchNode (σ : PM) (s t : HNode) (k : PM → SearchM Bool) : SearchM Bool := do
  match s, t with
  | .var _ x A, .var _ y B =>
    let some σ := (σ.bind x y).bind (·.matchTm A B) | return false
    k σ
  | .arrow _ d c, .arrow _ d' c' =>
    -- the conclusion first: it points at the domain
    matchProd σ c c' fun σ => matchProd σ d d' k
  | .conn _ kk a b ha hb, .conn _ kk' a' b' ha' hb' =>
    if kk != kk' then return false
    if ha == ha' && hb == hb' then
      if ← matchProd σ a a' fun σ => matchProd σ b b' k then return true
    if ha == hb' && hb == ha' then matchProd σ a b' fun σ => matchProd σ b a' k else return false
  | .eqn _ T a b ha hb, .eqn _ T' a' b' ha' hb' =>
    let some σ := σ.matchTm T T' | return false
    if ha == ha' && hb == hb' then
      if let some σ := (σ.matchTm a a').bind (·.matchTm b b') then
        if ← k σ then return true
    unless ha == hb' && hb == ha' do return false
    tick
    let some σ := (σ.matchTm a b').bind (·.matchTm b a') | return false
    k σ
  | _, _ => return false
end

/-- Are the two prepared graphs isomorphic? `false` also when the search exceeds `budget`. -/
def iso (g g' : HGraph) (budget : Nat) : Bool :=
  g.sig == g'.sig &&
  match (matchProd {} g.nodes g'.nodes fun _ => pure true).run budget with
  | .ok r _ => r
  | .error .. => false

/-! ## The bucket key -/

namespace Shape

def mix (a b : Nat) : Nat := (a * 1000003 + b + 1) % 4294967291

def sym (a b : Nat) : Nat := mix (a + b) (a * b)

/-- A hash of the shape of a label with the pointers erased, atom `k` hashed as `h k`. -/
def shape (h : Nat → Nat) : Tm → Nat
  | .bvar k => mix 1 k
  | .fvar _ => 2
  | .atom k => mix 3 (h k)
  | .app f a => mix (mix 4 (shape h f)) (shape h a)
  | .lam A b => mix (mix 5 (shape h A)) (shape h b)
  | .tpi A B => mix (mix 6 (shape h A)) (shape h B)
  | .unit => 7
  | .tt => 8
  | .pi A B => mix (mix 9 (shape h A)) (shape h B)
  | .sigma k A B => mix (mix (mix 10 (if k == .ex then 0 else 1)) (shape h A)) (shape h B)
  | .pair T a b => mix (mix (mix 11 (shape h T)) (shape h a)) (shape h b)
  | .proj k t => mix (mix 12 (if k then 1 else 0)) (shape h t)
  | .conn k A B => mix (mix (mix 13 (if k == .or then 0 else 1)) (shape h A)) (shape h B)
  | .eq T a b => mix (mix (mix 14 (shape h T)) (shape h a)) (shape h b)

end Shape

mutual
/-- The bucket key of a normal form, atom `k` hashed as `h k`. -/
def Graph.shapeSig (h : Nat → Nat) : Graph → Nat
  | [] => 0
  | n :: g => Node.shapeSig h n + Graph.shapeSig h g
def Node.shapeSig (h : Nat → Nat) : Node → Nat
  | .var _ A => Shape.mix 20 (Shape.shape h A)
  | .arrow d c => Shape.mix (Shape.mix 21 (Graph.shapeSig h d)) (Graph.shapeSig h c)
  | .conn k a b =>
    Shape.mix (Shape.mix 22 (if k == .or then 0 else 1)) (Shape.sym (Graph.shapeSig h a) (Graph.shapeSig h b))
  | .eqn T a b => Shape.mix (Shape.mix 23 (Shape.shape h T)) (Shape.sym (Shape.shape h a) (Shape.shape h b))
end

end DuplicateDependentTypes
