import Lean

def f (x := 0) (y := 1) : Nat :=
  x + y

open Lean Meta

/--
info: Nat → Nat → Nat
-/
#guard_msgs in
run_meta do
  let info ← getConstInfo ``f
  logInfo (← elimOptParam info.type)
