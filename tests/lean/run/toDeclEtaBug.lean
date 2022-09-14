import Lean

open Lean Compiler LCNF Testing

@[inline] def f (c b : Bool) (x : Nat) : Nat :=
  if c && b then
    x + 1
  else
    x + 2

def g (c : Nat) : Nat :=
  f true false c

#eval Lean.Compiler.compile #[``g]

@[cpass] def cseSizeTest : PassInstaller := Testing.assertNoFun |>.install `specialize `noFun

set_option trace.Compiler.result true
#eval Lean.Compiler.compile #[``g]
