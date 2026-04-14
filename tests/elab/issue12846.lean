module

set_option backward.do.legacy false

/--
error: Type mismatch. The rest of the `do` block has monadic result type
  Bool
but is expected to have monadic result type
  Unit
-/
#guard_msgs in
def test : IO Bool := do
  let a ← pure 25

/--
error: Type mismatch. The rest of the `do` block has monadic result type
  Bool
but is expected to have monadic result type
  Unit
-/
#guard_msgs in
def test2 : IO Bool := do
  let a := 25
