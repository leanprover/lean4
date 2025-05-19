import Lean.Server.Test.Cancel
open Lean.Server.Test.Cancel

/-!
The following should not deadlock: The `simp` tactic should be able to use `a_eq_b` even before
that theorem body is evaluated.
-/

set_option experimental.tactic.simp.useRflAttr true

set_option trace.Elab.block true
set_option debug.skipKernelTC true

opaque a : Nat
opaque b : Nat

theorem a_eq_b : a = b := by
  wait_for_unblock
  -- sleep 10000
  sorry

theorem bar : 2 * a = 3 * b := by
  -- unblock
  -- simp -dsimp only [a_eq_b]
  congr 1
  · sorry
  · apply a_eq_b
  skip
  -- unblock
