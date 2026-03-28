/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util
import Lean.Meta.Tactic.Grind.MBTC
import Lean.Meta.Tactic.Grind.Arith.ModelUtil
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Model
public section
namespace Lean.Meta.Grind.Arith.Cutsat

private def getAssignmentExt? (e : Expr) : GoalM (Option Rat) := do
  if let some val ← getAssignment? (← get) e then
    -- Easy case when `e : Int`
    return some val
  /-
  **Note**: The following code assumes that instantiated mvars occurring in types
  have been instantiated.
  -/
  let type ← inferType e
  if type == Int.mkType then
    -- It should have been handled in the previous getAssignment?
    return none
  else if type == Nat.mkType then
    -- TODO: improve this case.
    for parent in (← getParents e).elems do
      let_expr NatCast.natCast _ inst _ := parent | pure ()
      let_expr instNatCastInt := inst | pure ()
      return (← getAssignment? (← get) parent)
  else
    -- It may be a `ToInt` term.
    if let some x := (← get').toIntVarMap.find? { expr := e } then
      -- If there is an int variable `x` for `toInt e`, use its assignment.
      if let some val ← getAssignment? (← get) x then
        return some val
    if let some info := (← get').toIntTermMap.find? { expr := e } then
      -- If `toInt e` is an integer value, return it.
      if let some val ← getIntValue? info.eToInt then
        return some val
      -- If `toInt e` is a composite int term that has been internalized
      -- and has an assignment, return it.
      if (← alreadyInternalized info.eToInt) then
        if let some val ← getAssignment? (← get) info.eToInt then
          return some val
  return none

private def hasTheoryVar (e : Expr) : GoalM Bool := do
  cutsatExt.hasTermAtRoot e

/-
**Note**: cutsat is a procedure for linear integer arithmetic. Thus, morally a
nonlinear multiplication, division, and modulo are **not** interpreted by cutsat.
Thus, we enable model-theory combination for them. This is necessary for examples
such as:
```
example {a b : Nat} (ha : 1 ≤ a) : (a - 1 + 1) * b = a * b := by grind
```
Note that we currently use a restrictive/cheaper version of mbtc. We only case-split
on `a = b`, if they have the same assignment **and** occur as the `i`-th argument of
the same function symbol. The latter reduces the number of case-splits we have to
perform, but misses the following variant of the problem above.
```
example {a b : Nat} (ha : 1 ≤ a) : (a - 1 + 1) * b = b * a := by grind
```
If this becomes an issue in practice, we can add a flag for enabling the more
expensive version of `mbtc`.
-/

private def isNonlinearTerm (e : Expr) : GoalM Bool :=
  match_expr e with
  | HMul.hMul _ _ _ _ a b => return (← getIntValue? a <|> getIntValue? b).isNone
  | HDiv.hDiv _ _ _ _ _ b => return (← getIntValue? b).isNone
  | HMod.hMod _ _ _ _ _ b => return (← getIntValue? b).isNone
  | _ => return false

private def isInterpreted (e : Expr) : GoalM Bool := do
  if isInterpretedTerm e then
    return !(← isNonlinearTerm e)
  let f := e.getAppFn
  /-
  **Note**: `grind` normalizes terms, but some of them cannot be rewritten by `simp` because
  the rewrite would produce a type incorrect term. Thus, we may have `LT.lt` applications in
  the goal.
  -/
  return f.isConstOf ``LE.le || f.isConstOf ``Dvd.dvd || f.isConstOf ``LT.lt

private def eqAssignment (a b : Expr) : GoalM Bool := do
  let some v₁ ← getAssignmentExt? a | return false
  let some v₂ ← getAssignmentExt? b | return false
  return v₁ == v₂

def mbtc : GoalM Bool := do
  Grind.mbtc {
    hasTheoryVar := hasTheoryVar
    isInterpreted := isInterpreted
    eqAssignment := eqAssignment
  }

end Lean.Meta.Grind.Arith.Cutsat
