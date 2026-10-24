import Lean
import DuplicateDependentTypes.Encode

/-!
# Constant classes

Projects that copy code (a "kit" of definitions and lemmas pasted into several files under
different namespaces) produce constants that are equal up to the names of other copied
constants. Their theorems never match: the atoms `A.Kit.foo` and `B.Kit.foo` differ.

The classes are computed bottom-up over the constants of the analysed modules (private and
auxiliary ones included), in declaration order:

* a definition, opaque constant or instance is keyed by its level arity, type and value, a
  theorem by its level arity and type (proof irrelevance), an inductive type by its parameters,
  indices, type and the names and types of its constructors;
* in a key every constant of the analysed modules is replaced by the representative of its
  class (computed first, recursively), structure projections too; constructors and recursors
  follow their inductive type; references back into an inductive being keyed (its constructors'
  types) become a placeholder;
* universe parameters are renamed positionally; binder names and annotations are ignored
  (`Expr.eqv`).

The first constant with a key represents it. `ConstClasses.apply` rewrites an expression to the
representatives, so statements about copies of a kit become equal.
-/

namespace DuplicateDependentTypes

open Lean

structure ConstClasses where
  /-- Constant ↦ the representative of its class, for constants that do not represent it. -/
  rep : Std.HashMap Lean.Name Lean.Name := {}
  /-- The classes with at least two members, representative first. -/
  classes : Array (Array Lean.Name) := #[]
  deriving Inhabited

def ConstClasses.repOf (c : ConstClasses) (n : Lean.Name) : Lean.Name := c.rep.getD n n

/-- `e` with every constant and projection replaced by the representative of its class. -/
partial def ConstClasses.apply (c : ConstClasses) (e : Expr) : Expr :=
  if c.rep.isEmpty then e else
  e.replace fun
    | .const n ls => some (.const (c.repOf n) ls)
    | .proj s i x => some (.proj (c.repOf s) i (c.apply x))
    | _ => none

namespace Classes

/-- Placeholder for a reference into the inductive type being keyed. -/
def selfName : Lean.Name := `_dupdeps_self

structure State where
  rep : Std.HashMap Lean.Name Lean.Name := {}
  byKey : Std.HashMap Expr Lean.Name := {}
  members : Std.HashMap Lean.Name (Array Lean.Name) := {}
  visiting : Std.HashSet Lean.Name := {}

abbrev M := ReaderT (Environment × (Lean.Name → Bool)) (StateM State)

/-- Projections as applications of a marker, so that their structure is a constant too. -/
partial def projToApp (e : Expr) : Expr :=
  e.replace fun
    | .proj s i x => some (mkApp3 (.const `_dupdeps_proj []) (.const s []) (mkRawNatLit i) (projToApp x))
    | _ => none

/-- Replace the constants of `e` by their representatives (in `m`). -/
def rename (m : Std.HashMap Lean.Name Lean.Name) (e : Expr) : Expr :=
  e.replace fun
    | .const n ls => some (.const (m.getD n n) ls)
    | _ => none

def canonType (ci : ConstantInfo) (e : Expr) : Expr :=
  e.instantiateLevelParams ci.levelParams ((List.range ci.levelParams.length).map (.param <| canonLevelName ·))

/-- Record `n` under `k`: the first constant with a key represents it. -/
def keyed (n : Lean.Name) (k : Expr) : M Lean.Name := do
  match (← get).byKey[k]? with
  | some r =>
    modify fun s => { s with members := s.members.modify r (·.push n) }
    return r
  | none =>
    modify fun s => { s with byKey := s.byKey.insert k n, members := s.members.insert n #[n] }
    return n

mutual
/-- The representative of `n`'s class. -/
partial def repM (n : Lean.Name) : M Lean.Name := do
  let (env, sel) ← read
  unless sel n do return n
  if let some r := (← get).rep[n]? then return r
  if (← get).visiting.contains n then return selfName
  let some ci := env.find? n | return n
  modify fun s => { s with visiting := s.visiting.insert n }
  let r ← match ci with
    | .ctorInfo v => pure (n.replacePrefix v.induct (← repM v.induct))
    | .recInfo v => pure (n.replacePrefix v.getMajorInduct (← repM v.getMajorInduct))
    | .axiomInfo _ | .quotInfo _ => pure n
    | .thmInfo _ => keyed n (← key ci #[`thm] #[ci.type])
    | .defnInfo v => keyed n (← key ci #[`defn] #[ci.type, v.value])
    | .opaqueInfo v => keyed n (← key ci #[`opaque] #[ci.type, v.value])
    | .inductInfo v =>
      let ctors ← v.ctors.filterMapM fun c => do
        let some (.ctorInfo cv) := env.find? c | return none
        return some (cv.type, c.componentsRev.head!.toString)
      keyed n (← key ci (#[`induct, .mkNum .anonymous v.numParams, .mkNum .anonymous v.numIndices] ++
          ctors.toArray.map (Lean.Name.mkSimple ·.2)) (#[ci.type] ++ ctors.toArray.map (·.1)))
  modify fun s => { s with rep := s.rep.insert n r, visiting := s.visiting.erase n }
  return r

/-- The key: a tag, the level arity and the parts with their constants renamed. -/
partial def key (ci : ConstantInfo) (tag : Array Lean.Name) (parts : Array Expr) : M Expr := do
  let parts := parts.map (projToApp ∘ canonType ci)
  let mut m : Std.HashMap Lean.Name Lean.Name := {}
  for e in parts do
    for c in e.getUsedConstants do
      unless m.contains c do m := m.insert c (← repM c)
  let tagE := tag.foldl (fun e t => mkApp e (.const t [])) (.const `_dupdeps_key [])
  return mkAppN tagE (#[mkRawNatLit ci.levelParams.length] ++ parts.map (rename m))
end

end Classes

/-- The classes of the constants of the modules below `prefixes`. -/
def computeClasses (prefixes : Array Lean.Name) (isBelow : Array Lean.Name → Lean.Name → Bool) :
    CoreM ConstClasses := do
  let env ← getEnv
  let below := isBelow prefixes
  let names := env.header.moduleNames
  let mut order : Array Lean.Name := #[]
  for idx in [:names.size] do
    if below names[idx]! then order := order ++ env.header.moduleData[idx]!.constNames
  let selected : Std.HashSet Lean.Name := order.foldl (·.insert ·) {}
  let sel := fun n => selected.contains n
  let ((), st) := (order.forM fun n => discard (Classes.repM n)).run (env, sel) |>.run {}
  let rep := st.rep.fold (fun m n r => if n == r then m else m.insert n r) {}
  let classes := order.filterMap fun n => match st.members[n]? with
    | some ms => if ms.size ≥ 2 then some ms else none
    | none => none
  return { rep, classes }

end DuplicateDependentTypes
