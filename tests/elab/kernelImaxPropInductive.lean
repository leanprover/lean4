import Lean.CoreM
import Lean.AddDecl

/-!
The inductive checker must decide "is this an inductive predicate?" up to level
normalization, so that `Sort (imax 1 0)` and `Sort 0` are treated identically.
-/

open Lean

private def imaxProp : Expr := .sort (.imax (.succ .zero) .zero)

-- A data field is allowed because the type is an inductive predicate.
#eval show CoreM Unit from
  addDecl <| .inductDecl [] 0 [
    { name := `KIPData
      type := imaxProp
      ctors := [{ name := `KIPData.mk
                  type := .forallE `b (.const ``Bool []) (.const `KIPData []) .default }] }
  ] false

-- Nullary single constructor, once as `Sort (imax 1 0)` and once as `Sort 0`.
#eval show CoreM Unit from do
  addDecl <| .inductDecl [] 0 [
    { name := `KIPUnit, type := imaxProp
      ctors := [{ name := `KIPUnit.mk, type := .const `KIPUnit [] }] }] false
  addDecl <| .inductDecl [] 0 [
    { name := `KIPUnit0, type := .sort .zero
      ctors := [{ name := `KIPUnit0.mk, type := .const `KIPUnit0 [] }] }] false

-- The data field keeps the recursor in `Prop`; it is not an index.
#eval show CoreM Unit from do
  let .recInfo v ← getConstInfo `KIPData.rec | throwError "not a recursor"
  unless v.levelParams.isEmpty do throwError "expected `Prop`-only elimination"

-- Both spellings agree on K-like reduction and on the elimination level.
#eval show CoreM Unit from do
  let .recInfo v ← getConstInfo `KIPUnit.rec | throwError "not a recursor"
  let .recInfo v0 ← getConstInfo `KIPUnit0.rec | throwError "not a recursor"
  unless v.k == v0.k && v.levelParams.length == v0.levelParams.length do
    throwError "kernel treats `Sort (imax 1 0)` differently from `Sort 0`"
