def f (x : Nat) := x + 1

example : f x = x + 1 := rfl

/--
error: type mismatch
  rfl
has type
  f x = f x : Prop
but is expected to have type
  f x = x + 1 : Prop
-/
#guard_msgs in
seal f in
example : f x = x + 1 := rfl

example : f x = x + 1 := rfl

seal f

/--
error: type mismatch
  rfl
has type
  f x = f x : Prop
but is expected to have type
  f x = x + 1 : Prop
-/
#guard_msgs in
example : f x = x + 1 := rfl

unseal f

example : f x = x + 1 := rfl
