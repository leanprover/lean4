/-
Test that try? runs user suggestion tactics in parallel via attempt_all_par.

This test uses IO.stdGenRef (a builtin_initialize ref) to demonstrate parallelism:
- Tactic 1 (high prio): waits 1000ms, then checks if the random seed was changed
- Tactic 2 (low prio): immediately sets the seed to a magic value, then succeeds

If sequential: Tactic 1 executes first, waits, seed unchanged, fails.
              Then tactic 2 executes, sets seed, succeeds. Only one suggestion.
If parallel: Both tactics start together. Tactic 2 sets seed immediately.
            Tactic 1 waits 1000ms, sees changed seed, succeeds. Two suggestions.
-/
module
public import Lean
public meta import Lean.Elab.Tactic.Try

open Lean Meta Elab Tactic Try

-- An opaque goal that built-in tactics (including solve_by_elim) won't solve.
-- The axiom name starts with `_` so that `exact?` treats it as an implementation detail and
-- won't suggest it directly, allowing us to test parallelism of user-defined suggestion generators.
opaque ParallelTestGoal : Prop
axiom _parallelTestGoalHolds : ParallelTestGoal

-- Magic seed value to signal parallelism
meta def magicSeed : Nat := 314159265

-- Tactic that waits, then checks if seed was changed
elab "wait_and_check_seed" : tactic => do
  IO.sleep 1000
  let gen ← IO.stdGenRef.get
  let expected := mkStdGen magicSeed
  if gen.s1 == expected.s1 && gen.s2 == expected.s2 then
    evalTactic (← `(tactic| exact _parallelTestGoalHolds))
  else
    throwError "seed not changed (sequential execution detected)"

-- Tactic that immediately sets seed and succeeds
elab "set_seed_and_succeed" : tactic => do
  IO.setRandSeed magicSeed
  evalTactic (← `(tactic| exact _parallelTestGoalHolds))

-- Register both tactics as user suggestions
-- High priority tactic: reset seed first (to ensure clean state), then return waiting tactic
@[local try_suggestion 900]
meta def waitAndCheckSolver (_goal : MVarId) (_info : Try.Info) : MetaM (Array (TSyntax `tactic)) := do
  -- Reset to a different seed to ensure we're testing actual communication
  IO.setRandSeed 0
  return #[← `(tactic| wait_and_check_seed)]

-- Low priority tactic returns the seed-setting tactic
@[local try_suggestion 800]
meta def setFlagSolver (_goal : MVarId) (_info : Try.Info) : MetaM (Array (TSyntax `tactic)) := do
  return #[← `(tactic| set_seed_and_succeed)]

-- If parallel: both tactics succeed (tactic 1 sees seed change after waiting)
-- If sequential: only tactic 2 succeeds (tactic 1 sees unchanged seed)
/--
info: Try these:
  [apply] wait_and_check_seed
  [apply] set_seed_and_succeed
-/
#guard_msgs in
example : ParallelTestGoal := by
  try?
