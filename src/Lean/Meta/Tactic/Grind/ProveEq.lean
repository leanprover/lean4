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
Helper function for executing `x` with a fresh `newFacts` and without modifying
the goal state.
 -/
private def withoutModifyingState (x : GoalM α) : GoalM α := do
  let saved ← get
  modify fun goal => { goal with newFacts := {} }
  try
    x
  finally
    set saved

/--
If `e` has not been internalized yet, instantiate metavariables, unfold reducible, canonicalize,
and internalize the result.

This is an auxliary function used at `proveEq?` and `proveHEq?`.
-/
private def ensureInternalized (e : Expr) : GoalM Expr := do
  if (← alreadyInternalized e) then
    return e
  else
    /-
    It is important to expand reducible declarations. Otherwise, we cannot prove
    `¬ a = []` and `b ≠ []` by congruence closure even when `a` and `b` are in the same
    equivalence class.
    -/
    let e ← shareCommon (← canon (← unfoldReducible (← instantiateMVars e)))
    internalize e 0
    return e

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
  trace[grind.debug.proveEq] "({lhs}) = ({rhs})"
  if (← alreadyInternalized lhs <&&> alreadyInternalized rhs) then
    if (← isEqv lhs rhs) then
      return some (← mkEqProof lhs rhs)
    else
      return none
  else withoutModifyingState do
    /-
    We used to apply the `grind` normalizer, but it created unexpected failures.
    Here is an example, suppose we are trying to prove `i < (a :: l).length` is equal to `0 < (a :: l).length`
    when `i` and `0`  are in the same equivalence class. This should hold by applying congruence closure.
    However, if we apply the normalizer, we obtain `i+1 ≤ (a :: l).length` and `1 ≤ (a :: l).length`, and
    the equality cannot be detected by congruence closure anymore.
    -/
    let lhs ← ensureInternalized lhs
    let rhs ← ensureInternalized rhs
    processNewFacts
    unless (← isEqv lhs rhs) do return none
    unless (← hasSameType lhs rhs) do return none
    mkEqProof lhs rhs

/-- Similiar to `proveEq?`, but for heterogeneous equality. -/
def proveHEq? (lhs rhs : Expr) : GoalM (Option Expr) := do
  if (← alreadyInternalized lhs <&&> alreadyInternalized rhs) then
    if (← isEqv lhs rhs) then
      return some (← mkHEqProof lhs rhs)
    else
      return none
  else withoutModifyingState do
    -- See comment at `proveEq?`
    let lhs ← ensureInternalized lhs
    let rhs ← ensureInternalized rhs
    processNewFacts
    unless (← isEqv lhs rhs) do return none
    mkHEqProof lhs rhs

end Lean.Meta.Grind
