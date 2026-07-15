prelude
import Init.Notation
/-!
Tests `autoTry.onUnsolvedGoal` in a restricted (prelude) environment. The `try?`
machinery references constants (`Lean.Parser.Tactic.solveByElim` etc.) that are not yet
available in the prelude, so the linter surfaces an "Unknown constant" error. This is
expected and documented here so we notice if the behaviour changes; a future improvement
would teach autoTry to detect missing infrastructure and silently no-op instead.
-/

set_option autoTry.onUnsolvedGoal true

/--
error: unsolved goals
⊢ True
---
error: linter _private.Lean.Elab.Tactic.AutoTry.0.Lean.Elab.Tactic.AutoTry.autoTryHook failed: Unknown constant `Lean.Parser.Tactic.solveByElim`
-/
#guard_msgs in
theorem test : True := by
