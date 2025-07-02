def foo (x : Nat) (y : Bool) (z : Nat) (w : Nat) := ()
/--
error: Application type mismatch: In the application
  foo 1 true true
the last
  true
argument has type
  Bool
but is expected to have type
  Nat
-/
#guard_msgs in
#eval foo 1 true true 1
