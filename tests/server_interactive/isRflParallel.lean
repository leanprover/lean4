import Lean.Server.Test.Cancel

open Lean Meta

/-!
The following should not deadlock: The `simp` tactic should be able to use `a_eq_b` even before
that theorem body is evaluated.

TODO: Doesn't work any more with the rfl extension being .async, as that waits for the body to be
evaluated.
-/

-- set_option trace.Elab.block true
set_option debug.skipKernelTC true
set_option backward.dsimp.useDefEqAttr false
set_option debug.tactic.simp.checkDefEqAttr false

axiom testSorry : α

opaque a : Nat
opaque b : Nat

theorem a_eq_b : a = b := by
  -- Three possible ways to pretend this theorem takes a long time:

  -- wait_for_unblock_async

  -- run_tac
  --   while true do
  --     if (← Server.Test.Cancel.unblockedCancelTk.isSet) then
  --       break
  --     IO.sleep 30

  -- sleep 100000
  exact testSorry

theorem bar : 2 * a = 2 * b := by
  congr 1
  -- apply a_eq_b
  simp only [a_eq_b]
  run_tac
    Server.Test.Cancel.unblockedCancelTk.set
