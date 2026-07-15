module

set_option backward.do.legacy false

-- Original issue: `let x ← value` as last element in non-Unit do block
/--
error: Type mismatch. The `do` element has monadic result type
  Unit
but the rest of the `do` block has monadic result type
  Bool
-/
#guard_msgs in
def test_letArrow : IO Bool := do
  let a ← pure 25

/--
error: Type mismatch. The `do` element has monadic result type
  Unit
but the rest of the `do` block has monadic result type
  Bool
-/
#guard_msgs in
def test_let : IO Bool := do
  let a := 25

-- `have` as last element
/--
error: Type mismatch. The `do` element has monadic result type
  Unit
but the rest of the `do` block has monadic result type
  Bool
-/
#guard_msgs in
def test_have : IO Bool := do
  have a := 25

-- `let rec` as last element
/--
error: Type mismatch. The `do` element has monadic result type
  Unit
but the rest of the `do` block has monadic result type
  Bool
-/
#guard_msgs in
def test_letRec : IO Bool := do
  let rec f : Nat → Nat
    | 0 => 0
    | n + 1 => f n

-- `for` as last element
/--
error: Type mismatch. The `do` element has monadic result type
  Unit
but the rest of the `do` block has monadic result type
  Bool
-/
#guard_msgs in
def test_for : IO Bool := do
  for _ in [1, 2, 3] do
    pure ()

-- `dbg_trace` as last element
/--
error: Type mismatch. The `do` element has monadic result type
  Unit
but the rest of the `do` block has monadic result type
  Bool
-/
#guard_msgs in
def test_dbgTrace : IO Bool := do
  dbg_trace "hello"

-- `assert!` as last element
/--
error: Type mismatch. The `do` element has monadic result type
  Unit
but the rest of the `do` block has monadic result type
  Bool
-/
#guard_msgs in
def test_assert : IO Bool := do
  assert! true

-- `if` without else as last element
/--
error: Application type mismatch: The argument
  ()
has type
  Unit
but is expected to have type
  Bool
in the application
  pure ()
---
error: Type mismatch. The `do` element has monadic result type
  Unit
but the rest of the `do` block has monadic result type
  Bool
-/
#guard_msgs in
def test_if_no_else : IO Bool := do
  if true then
    pure ()

-- `if` with else works fine when branches match the result type
#guard_msgs in
def test_if_else_ok : IO Bool := do
  if true then pure true else pure false
