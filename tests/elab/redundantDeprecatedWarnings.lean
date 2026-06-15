set_option linter.deprecated true

def foo (x : Nat) := x + 1

theorem bar (x : Nat) : foo x = x + 1 := rfl

@[deprecated foo (since:="2025-06-23")]
def baz (x : Nat) := x + 1

@[deprecated foo (since:="2025-06-23")]
def baz2 (x : Nat) := x + 1

@[simp,deprecated bar (since:="2025-06-23")]
theorem qux (x : Nat) : foo x = baz x := rfl

@[deprecated bar (since:="2025-06-23")]
theorem quux (x : Nat) : foo x = x + 1 := by
  rw [qux x]
  rfl

@[simp, deprecated bar (since:="2025-06-23")]
theorem qux2 (x : Nat) : foo x = baz x := rfl

@[deprecated "test" (since:="2025-06-23")]
inductive Hello : Prop where
  | mk (n : Nat) : baz n = 7 → Hello

@[deprecated "test" (since:="2025-06-23")]
coinductive Hello2 : Prop where
  | mk (n : Nat) : baz n = 7 → Hello2

@[deprecated "test" (since:="2025-06-23")]
inductive Hello3 (h : baz n = 7) where

@[deprecated "test" (since:="2025-06-23")]
axiom ax : baz n = 7

@[deprecated "test" (since:="2025-06-23")]
structure MyStruct where
  n : Nat
  hp : baz n = 7

@[deprecated "test" (since:="2025-06-23")]
structure MyStruct2 (n : Nat) (hp : baz n = 7) where

@[deprecated "test" (since:="2025-06-23")]
def myFun (n : Nat) : Nat := Id.run do
  return baz n

@[deprecated "test" (since:="2025-06-23")]
instance : BEq Nat where
  beq m n := m == baz n

/-- warning: `baz` has been deprecated: Use `foo` instead -/
#guard_msgs in
mutual
  inductive NotDep : Prop where
    | mk : baz 0 = 0 → NotDep → DepInd → NotDep
  @[deprecated "test" (since:="2025-06-23")]
  inductive DepInd : Prop where
    | mk : baz2 0 = 0 → NotDep → DepInd → DepInd
end
