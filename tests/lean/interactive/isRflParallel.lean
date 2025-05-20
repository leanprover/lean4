import Lean.Server.Test.Cancel

open Lean Meta

/-!
The following should not deadlock: The `simp` tactic should be able to use `a_eq_b` even before
that theorem body is evaluated.

TODO: Does't work any more with the rfl extension being .async, as that waits for the body to be
evaluated.
-/

set_option experimental.tactic.simp.useRflAttr true
set_option trace.Meta.Tactic.simp.rflAttrMismatch false

set_option trace.Elab.block true
-- set_option debug.skipKernelTC true

axiom testSorry : α

opaque a : Nat
opaque b : Nat

theorem a_eq_b : a = b := by
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
  -- apply _root_.a_eq_b
  simp only [_root_.a_eq_b]
  run_tac
    Server.Test.Cancel.unblockedCancelTk.set
