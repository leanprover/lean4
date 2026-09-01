/-
Tests for heartbeat management in `try?`

This file tests that:
1. Each tactic execution gets a fresh heartbeat budget with the original limit
2. Tactics that exceed heartbeat limits are filtered out from try? suggestions
3. `attempt_all` continues past heartbeat failures to find working tactics
-/

module
public import Lean
public meta import Lean.Elab.Tactic.Try

open Lean Meta Elab Tactic Try

-- Define an opaque proposition that built-in tactics (including solve_by_elim) won't solve
opaque CustomGoal : Prop
axiom customGoalHolds : CustomGoal

-- Create a tactic that consumes heartbeats through meta operations
elab "expensive_meta_tactic" : tactic => do
  for _ in [:10000] do
    let mvar ← mkFreshExprMVar (some (mkConst ``Nat))
    let _ ← instantiateMVars mvar
  evalTactic (← `(tactic| exact customGoalHolds))

-- Verify that expensive_meta_tactic actually consumes heartbeats:
-- It times out at 100 heartbeats
set_option maxHeartbeats 100 in
/--
error: (deterministic) timeout at `«tactic execution»`, maximum number of heartbeats (100) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
example : CustomGoal := by
  expensive_meta_tactic

-- It succeeds with 500 heartbeats (establishes threshold)
set_option maxHeartbeats 500 in
#guard_msgs in
example : CustomGoal := by
  expensive_meta_tactic

-- Now register it as a try? suggestion along with a cheap alternative
@[local try_suggestion 900]
meta def expensiveSolver (_ : MVarId) (_ : Try.Info) : MetaM (Array (TSyntax `tactic)) := do
  return #[← `(tactic| expensive_meta_tactic)]

@[local try_suggestion 700]
meta def cheapSolver (_ : MVarId) (_ : Try.Info) : MetaM (Array (TSyntax `tactic)) := do
  return #[← `(tactic| exact customGoalHolds)]


-- With 100 heartbeats
-- expensive_meta_tactic should be filtered out from try? suggestions
-- Only `customGoalHolds`` should appear
set_option maxHeartbeats 100 in
/--
info: Try this:
  [apply] exact customGoalHolds✝
-/
#guard_msgs in
example : CustomGoal := by
  try?

-- With 500 heartbeats, both should appear.
/--
info: Try these:
  [apply] expensive_meta_tactic
  [apply] exact customGoalHolds✝
-/
#guard_msgs in
set_option maxHeartbeats 500 in
example : CustomGoal := by
  try?
