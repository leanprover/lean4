/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.Tactic.Grind.Simp

namespace Lean.Meta.Grind

/--
Helper function for executing `x` with a fresh `newEqs` and without modifying
the goal state.
 -/
private def withoutModifyingState (x : GoalM α) : GoalM α := do
  let saved ← get
  modify fun goal => { goal with newEqs := {} }
  try
    x
  finally
    set saved

/--
If `e` has not been internalized yet, simplify it, and internalize the result.
-/
private def preprocessAndInternalize (e : Expr) (gen : Nat := 0) : GoalM Simp.Result := do
  if (← alreadyInternalized e) then
    return { expr := e }
  else
    let r ← preprocess e
    internalize r.expr gen
    return r

/--
Try to construct a proof that `lhs = rhs` using the information in the
goal state. If `lhs` and `rhs` have not been internalized, this function
will internalize then, process propagated equalities, and then check
whether they are in the same equivalence class or not.
The goal state is not modified by this function.
This function mainly relies on congruence closure, and constraint
propagation. It will not perform case analysis.
-/
def proveEq? (lhs rhs : Expr) : GoalM (Option Expr) := do
  if (← alreadyInternalized lhs <&&> alreadyInternalized rhs) then
    if (← isEqv lhs rhs) then
      return some (← mkEqProof lhs rhs)
    else
      return none
  else withoutModifyingState do
    let lhs ← preprocessAndInternalize lhs
    let rhs ← preprocessAndInternalize rhs
    processNewEqs
    unless (← isEqv lhs.expr rhs.expr) do return none
    unless (← hasSameType lhs.expr rhs.expr) do return none
    let h ← mkEqProof lhs.expr rhs.expr
    let h ← match lhs.proof?, rhs.proof? with
      | none,    none    => pure h
      | none,    some h₂ => mkEqTrans h (← mkEqSymm h₂)
      | some h₁, none    => mkEqTrans h₁ h
      | some h₁, some h₂ => mkEqTrans (← mkEqTrans h₁ h) (← mkEqSymm h₂)
    return some h

/-- Similiar to `proveEq?`, but for heterogeneous equality. -/
def proveHEq? (lhs rhs : Expr) : GoalM (Option Expr) := do
  if (← alreadyInternalized lhs <&&> alreadyInternalized rhs) then
    if (← isEqv lhs rhs) then
      return some (← mkHEqProof lhs rhs)
    else
      return none
  else withoutModifyingState do
    let lhs ← preprocessAndInternalize lhs
    let rhs ← preprocessAndInternalize rhs
    processNewEqs
    unless (← isEqv lhs.expr rhs.expr) do return none
    let h ← mkHEqProof lhs.expr rhs.expr
    let h ← match lhs.proof?, rhs.proof? with
      | none,    none    => pure h
      | none,    some h₂ => mkHEqTrans h (← mkHEqSymm h₂)
      | some h₁, none    => mkHEqTrans h₁ h
      | some h₁, some h₂ => mkHEqTrans (← mkHEqTrans h₁ h) (← mkHEqSymm h₂)
    return some h

end Lean.Meta.Grind
