set_option pp.mvars false

def f (x : Nat) := x + 1

example : f x = x + 1 := rfl

/--
error: Type mismatch
  rfl
has type
  ?_ = ?_
but is expected to have type
  f x = x + 1
-/
#guard_msgs in
seal f in
example : f x = x + 1 := rfl

example : f x = x + 1 := rfl

seal f

/--
error: Type mismatch
  rfl
has type
  ?_ = ?_
but is expected to have type
  f x = x + 1
-/
#guard_msgs in
example : f x = x + 1 := rfl

unseal f

example : f x = x + 1 := rfl
