/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Types
import Init.Grind.Lemmas
public section
namespace Lean.Meta.Grind

private def dummyEq : Expr := mkApp (mkConst ``Eq [1]) default

/--
Returns `some (c = d)` if
- `c = d` and `False` are in the same equivalence class, and
- `a` (`b`) and `c` are in the same equivalence class, and
- `b` (`a`) and `d` are in the same equivalence class.
Otherwise return `none`.

Remark `a` and `b` are assumed to have the same type.
-/
def getDiseqFor? (a b : Expr) : GoalM (Option Expr) := do
  let key := mkApp2 dummyEq a b
  let some { e := e' } := (← get).congrTable.find? { e := key } | return none
  if (← isEqFalse e') then
    return some e'
  else
    return none

/--
Returns `true` if `a` and `b` are known to be disequal.
See `getDiseqFor?`
-/
def isDiseq (a b : Expr) : GoalM Bool := do
  return (← getDiseqFor? a b).isSome

/--
Given an equality `eq` of the form `c = d` s.t. `eq` is `False`, and
`a = b` is congruent to `c = d`, return a proof for `a ≠ b`
-/
def mkDiseqProofUsing (a b : Expr) (eq : Expr) : GoalM Expr := do
  let_expr f@Eq α c d := eq | unreachable!
  let u := f.constLevels!
  let h := mkOfEqFalseCore eq (← mkEqFalseProof eq)
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

/--
Returns a proof for `true` if `a` and `b` are known to be disequal.
See `getDiseqFor?`
-/
def mkDiseqProof? (a b : Expr) : GoalM (Option Expr) := do
  let some eq ← getDiseqFor? a b | return none
  mkDiseqProofUsing a b eq

def mkDiseqProof (a b : Expr) : GoalM Expr := do
 let some h ← mkDiseqProof? a b
   | throwError "internal `grind` error, failed to build disequality proof for{indentExpr a}\nand{indentExpr b}"
  return h

end Lean.Meta.Grind
