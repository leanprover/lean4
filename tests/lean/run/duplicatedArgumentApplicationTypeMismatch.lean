def foo (x : Nat) (y : Bool) (z : Nat) (w : Nat) := ()
/--
error: Application type mismatch: In the appplication
  foo 1 true true
the final argument
  true
has type
  Bool : Type
but is expected to have type
  Nat : Type
-/
#guard_msgs in
#eval foo 1 true true 1
