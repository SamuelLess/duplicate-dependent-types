/-!
# Labels and dependency graphs

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

/-- Member names. -/
abbrev Var := Nat

inductive SigKind where
  | ex | and
  deriving BEq, Hashable, Inhabited

inductive Conn where
  | or | iff
  deriving BEq, Hashable, Inhabited

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
  deriving Inhabited

def Tm.size : Tm → Nat
  | app f a | lam f a | tpi f a | pi f a | sigma _ f a | conn _ f a => size f + size a + 1
  | pair T a b | eq T a b => size T + size a + size b + 1
  | proj _ t => size t + 1
  | _ => 1

inductive Node where
  | var : Var → Tm → Node
  | arrow : List Node → List Node → Node
  | conn : Conn → List Node → List Node → Node
  | eqn : Tm → Tm → Tm → Node
  deriving Inhabited

abbrev Graph := List Node

mutual
def Graph.size : Graph → Nat
  | [] => 0
  | n :: g => Node.size n + Graph.size g
def Node.size : Node → Nat
  | .var _ A => 1 + A.size
  | .arrow d c | .conn _ d c => 1 + Graph.size d + Graph.size c
  | .eqn T a b => 1 + T.size + a.size + b.size
end

end DuplicateDependentTypes
