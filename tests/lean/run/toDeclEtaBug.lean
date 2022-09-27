import Lean

open Lean Compiler LCNF Testing

@[inline] def f (c b : Bool) (x : Nat) : Nat :=
  if c && b then
    x + 1
  else
    x + 2

-- TODO: uncomment after the new compiler is executed by default
-- @[cpass] def cseSizeTest : PassInstaller := Testing.assertNoFun |>.install `specialize `noFun

def g (c : Nat) : Nat :=
  f true false c
