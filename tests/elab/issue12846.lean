module

set_option backward.do.legacy false

/--
error: Type mismatch. The `do` element has monadic result type
  Unit
but the rest of the `do` block has monadic result type
  Bool
-/
#guard_msgs in
def test : IO Bool := do
  let a ← pure 25

/--
error: Type mismatch. The `do` element has monadic result type
  Unit
but the rest of the `do` block has monadic result type
  Bool
-/
#guard_msgs in
def test2 : IO Bool := do
  let a := 25
