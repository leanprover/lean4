import Lean.Server.Test.Cancel
open Lean.Server.Test.Cancel

opaque a : Nat
opaque b : Nat

/-!
The following should not deadlock: The `simp` tactic should be able to use `a_eq_b` even before
that theorem body is evaluated.
-/

theorem a_eq_b : a = b := by
  wait_for_unblock
  sorry

example : 2 * a = 2 * b := by
  simp -dsimp [a_eq_b]
  unblock
