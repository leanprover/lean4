def foo (x : Nat) (y : Bool) (z : Nat) (w : Nat) := ()
/--
error: Application type mismatch: The last
  true
argument has type
  Bool
but is expected to have type
  Nat
in the application
  foo 1 true true
-/
#guard_msgs in
#eval foo 1 true true 1
