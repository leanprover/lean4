-- Test that `let pat : Type ← rhs` works in do-notation

-- Basic: anonymous constructor pattern with expected type
def test1 : Id (Nat × String) := do
  let ⟨x, y⟩ : Nat × String ← pure ⟨1, "hello"⟩
  return (x, y)

example : test1 = (1, "hello") := rfl

-- Tuple pattern with expected type
def test2 : Id (Nat × Nat) := do
  let (a, b) : Nat × Nat ← pure (2, 3)
  return (a + b, a * b)

example : test2 = (5, 6) := rfl

-- The expected type helps resolve what would otherwise be ambiguous
structure Dims where
  width : Nat
  height : Nat

def getDims : Id Dims := pure ⟨800, 600⟩

def test3 : Id Nat := do
  let ⟨w, h⟩ : Dims ← getDims
  return w * h

example : test3 = 480000 := rfl

-- With else branch
def test4 : Option Nat := do
  let .some x : Option Nat ← some (some 42)
    | none
  return x

example : test4 = some 42 := rfl

-- With else branch, taking the else
def test5 : Option Nat := do
  let .some _x : Option Nat ← some none
    | pure 99
  return _x

example : test5 = some 99 := rfl

-- Mutable let with pattern and type
def test6 : Id Nat := do
  let mut ⟨a, b⟩ : Nat × Nat ← pure (1, 2)
  a := a + 10
  b := b + 20
  return a + b

example : test6 = 33 := rfl

-- Without type annotation still works (regression test)
def test7 : Id Nat := do
  let (x, y) ← pure (1, 2)
  return x + y

example : test7 = 3 := rfl

-- Wildcard pattern with type
def test8 : Id Nat := do
  let _ : Nat ← pure 42
  return 0

example : test8 = 0 := rfl
