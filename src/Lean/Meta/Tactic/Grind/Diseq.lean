/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Grind.Lemmas
import Lean.Meta.Tactic.Grind.Types

namespace Lean.Meta.Grind

/--
Returns `some (c = d)` if
- `c = d` and `False` are in the same equivalence class, and
- `a` (`b`) and `c` are in the same equivalence class, and
- `b` (`a`) and `d` are in the same equivalence class.
Otherwise return `none`.

Remark `a` and `b` are assumed to have the same type.
-/
private def getDiseqFor? (a b : Expr) : GoalM (Option Expr) := do
  /-
  In Z3, we use the congruence table to find equalities more efficiently,
  but this optimization would be more complicated here because equalities have
  the type as an implicit argument, and `grind`s congruence table assumes it is
  hash-consed and canonicalized. So, we use the "slower" approach of visiting
  parents.
  -/
  let aRoot ← getRoot a
  let bRoot ← getRoot b
  let aParents ← getParents aRoot
  let bParents ← getParents bRoot
  if aParents.size ≤ bParents.size then
    go aParents
  else
    go bParents
where
  go (parents : ParentSet) : GoalM (Option Expr) := do
    for parent in parents do
      let_expr Eq α c d := parent | continue
      if (← isEqFalse parent) then
        -- Remark: we expect `hasType` test to seldom fail, but it can happen because of
        -- heterogeneous equalities
        if (← isEqv a c <&&> isEqv b d <&&> hasType a α) then
          return some parent
        if (← isEqv a d <&&> isEqv b c <&&> hasType a α) then
          return some parent
    return none

/--
Returns `true` if `a` and `b` are known to be disequal.
See `getDiseqFor?`
-/
def isDiseq (a b : Expr) : GoalM Bool := do
  return (← getDiseqFor? a b).isSome

/--
Returns a proof for `true` if `a` and `b` are known to be disequal.
See `getDiseqFor?`
-/
def mkDiseqProof? (a b : Expr) : GoalM (Option Expr) := do
  let some eq ← getDiseqFor? a b | return none
  let_expr f@Eq α c d := eq | unreachable!
  let u := f.constLevels!
  let h ← mkOfEqFalse (← mkEqFalseProof eq)
  let (c, d, h) ← if (← isEqv a c <&&> isEqv b d) then
    pure (c, d, h)
  else
    pure (d, c, mkApp4 (mkConst ``Ne.symm u) α c d h)
  -- We have `a = c` and `b = d`
  let h ← if isSameExpr a c then
    pure h
  else
    pure <| mkApp6 (mkConst ``Grind.ne_of_ne_of_eq_left u) α a c d (← mkEqProof a c) h
  -- `h : a ≠ d
  if isSameExpr b d then
    return h
  else
    return mkApp6 (mkConst ``Grind.ne_of_ne_of_eq_right u) α b a d (← mkEqProof b d) h

end Lean.Meta.Grind
