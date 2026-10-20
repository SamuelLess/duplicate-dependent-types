/-!
# The IR: labels and dependency graphs

A proposition is taken apart into a *graph*: a product (list, read up to order) of nodes

* `var x A`: a named member `x : A`, whose label may point at earlier members;
* `arrow Δ C`: `∀ Δ, C` between two products;
* `conn k a b`: `a ∨ b` / `a ↔ b`, sides unordered;
* `eqn T a b`: `a = b` at type `T`, sides unordered.

A product in an arrow domain is a Π-telescope, every other product a Σ-telescope ending in
`True`, so hypotheses, conjuncts and `∃`-binders are all members. Two statements are duplicates
when the normal forms of their graphs (`Normalize.lean`) are isomorphic (`Match.lean`): equal up to
renaming, reordering of every product and flipping of connective and equation sides.
-/

namespace DuplicateDependentTypes

/-- Node names. -/
abbrev Var := Nat

inductive SigKind where
  | ex   -- `∃ x : A, B`
  | and  -- `A ∧ B`
  deriving DecidableEq, Repr, Hashable, Inhabited

inductive Conn where
  | or | iff
  deriving DecidableEq, Repr, Hashable, Inhabited

/-- Labels. Bound variables are de Bruijn indices as in `Lean.Expr`; `fvar i` points at the
member named `i`; `atom k` is entry `k` of the atom table (an opaque closed Lean term). -/
inductive Tm where
  | bvar : Nat → Tm
  | fvar : Var → Tm
  | atom : Nat → Tm
  | app : Tm → Tm → Tm
  | lam : Tm → Tm → Tm                  -- `fun x : A => b`
  | tpi : Tm → Tm → Tm                  -- `(x : A) → B`, `B` not a Prop: opaque
  | unit : Tm                           -- `True`
  | tt : Tm                             -- `True.intro`
  | pi : Tm → Tm → Tm                   -- `∀ x : A, B`, `B : Prop`
  | sigma : SigKind → Tm → Tm → Tm      -- `∃ x : A, B` / `A ∧ B`
  | pair : Tm → Tm → Tm → Tm            -- `⟨a, b⟩ : T`
  | proj : Bool → Tm → Tm               -- `.1` (`false`), `.2` (`true`)
  | conn : Conn → Tm → Tm → Tm
  | eq : Tm → Tm → Tm → Tm              -- `@Eq T a b`
  deriving DecidableEq, Repr, Hashable, Inhabited

namespace Tm

def rename (φ : Var → Var) : Tm → Tm
  | fvar i => fvar (φ i)
  | app f a => app (rename φ f) (rename φ a)
  | lam A b => lam (rename φ A) (rename φ b)
  | tpi A B => tpi (rename φ A) (rename φ B)
  | pi A B => pi (rename φ A) (rename φ B)
  | sigma k A B => sigma k (rename φ A) (rename φ B)
  | pair T a b => pair (rename φ T) (rename φ a) (rename φ b)
  | proj k t => proj k (rename φ t)
  | conn k A B => conn k (rename φ A) (rename φ B)
  | eq T a b => eq (rename φ T) (rename φ a) (rename φ b)
  | t => t

def refs : Tm → List Var
  | fvar i => [i]
  | app f a | lam f a | tpi f a | pi f a | sigma _ f a | conn _ f a => refs f ++ refs a
  | pair T a b | eq T a b => refs T ++ refs a ++ refs b
  | proj _ t => refs t
  | _ => []

def mapAtoms (f : Nat → Nat) : Tm → Tm
  | atom k => atom (f k)
  | app a b => app (mapAtoms f a) (mapAtoms f b)
  | lam a b => lam (mapAtoms f a) (mapAtoms f b)
  | tpi a b => tpi (mapAtoms f a) (mapAtoms f b)
  | pi a b => pi (mapAtoms f a) (mapAtoms f b)
  | sigma k a b => sigma k (mapAtoms f a) (mapAtoms f b)
  | pair T a b => pair (mapAtoms f T) (mapAtoms f a) (mapAtoms f b)
  | proj k t => proj k (mapAtoms f t)
  | conn k a b => conn k (mapAtoms f a) (mapAtoms f b)
  | eq T a b => eq (mapAtoms f T) (mapAtoms f a) (mapAtoms f b)
  | t => t

def size : Tm → Nat
  | app f a | lam f a | tpi f a | pi f a | sigma _ f a | conn _ f a => size f + size a + 1
  | pair T a b | eq T a b => size T + size a + size b + 1
  | proj _ t => size t + 1
  | _ => 1

end Tm

inductive Node where
  | var : Var → Tm → Node
  | arrow : List Node → List Node → Node
  | conn : Conn → List Node → List Node → Node
  | eqn : Tm → Tm → Tm → Node
  deriving Repr, Inhabited

abbrev Graph := List Node

mutual
def Graph.beq : Graph → Graph → Bool
  | [], [] => true
  | n :: g, n' :: g' => Node.beq n n' && Graph.beq g g'
  | _, _ => false
def Node.beq : Node → Node → Bool
  | .var x A, .var y B => x == y && A == B
  | .arrow d c, .arrow d' c' => Graph.beq d d' && Graph.beq c c'
  | .conn k a b, .conn k' a' b' => k == k' && Graph.beq a a' && Graph.beq b b'
  | .eqn T a b, .eqn T' a' b' => T == T' && a == a' && b == b'
  | _, _ => false
end

namespace Graph

mutual
def refs : Graph → List Var
  | [] => []
  | n :: g => refsN n ++ refs g
def refsN : Node → List Var
  | .var _ A => A.refs
  | .arrow d c | .conn _ d c => refs d ++ refs c
  | .eqn T a b => T.refs ++ a.refs ++ b.refs
end

mutual
def names : Graph → List Var
  | [] => []
  | n :: g => namesN n ++ names g
def namesN : Node → List Var
  | .var x _ => [x]
  | .arrow d c | .conn _ d c => names d ++ names c
  | .eqn _ _ _ => []
end

mutual
def rename (φ : Var → Var) : Graph → Graph
  | [] => []
  | n :: g => renameN φ n :: rename φ g
def renameN (φ : Var → Var) : Node → Node
  | .var x A => .var (φ x) (A.rename φ)
  | .arrow d c => .arrow (rename φ d) (rename φ c)
  | .conn k a b => .conn k (rename φ a) (rename φ b)
  | .eqn T a b => .eqn (T.rename φ) (a.rename φ) (b.rename φ)
end

mutual
def size : Graph → Nat
  | [] => 0
  | n :: g => sizeN n + size g
def sizeN : Node → Nat
  | .var _ A => 1 + A.size
  | .arrow d c | .conn _ d c => 1 + size d + size c
  | .eqn T a b => 1 + T.size + a.size + b.size
end

partial def mapAtoms (f : Nat → Nat) (g : Graph) : Graph :=
  g.map fun
    | .var x A => .var x (A.mapAtoms f)
    | .arrow d c => .arrow (mapAtoms f d) (mapAtoms f c)
    | .conn k a b => .conn k (mapAtoms f a) (mapAtoms f b)
    | .eqn T a b => .eqn (T.mapAtoms f) (a.mapAtoms f) (b.mapAtoms f)

end Graph

end DuplicateDependentTypes
