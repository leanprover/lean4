import Lean

open Lean Meta Elab Tactic in
elab "my_tac" : tactic =>
  liftMetaTactic1 fun mvarId => do
    mvarId.assign (mkConst ``True.intro)
    return none

example : True := by
  my_tac -- should work

/--
error: (kernel) declaration type mismatch, '_example' has type
  True
but it is expected to have type
  1 = 2
-/
#guard_msgs in
example : 1 = 2 := by
  my_tac -- generates invalid proof that is rejected by the kernel

set_option debug.skipKernelTC true in
example : 1 = 2 := by
  my_tac -- generates invalid proof that is **not** checked by the kernel
