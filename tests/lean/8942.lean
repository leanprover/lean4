set_option linter.deprecated true

def foo (x : Nat) := x + 1

theorem bar (x : Nat) : foo x = x + 1 := rfl

@[deprecated foo (since:="2025-06-23")]
def baz (x : Nat) := x + 1

@[deprecated bar (since:="2025-06-23")]
theorem qux (x : Nat) : foo x = baz x := rfl

@[deprecated bar (since:="2025-06-23")]
theorem quux (x : Nat) : foo x = x + 1 := by
  rw [qux x]
  rfl

@[deprecated bar (since:="2025-06-23")]
theorem test_exact (x : Nat) : foo x = baz x := by
  exact qux x

@[deprecated bar (since:="2025-06-23")]
theorem test_simple (x : Nat) : foo x = baz x := qux x

-- Test deprecated inductive types
@[deprecated "Use List instead" (since:="2025-06-23")]
inductive DeprecatedList (α : Type) where
  | nil : DeprecatedList α
  | cons : α → DeprecatedList α → DeprecatedList α

-- Test using deprecated inductive type

@[deprecated "Use List instead" (since:="2025-06-23")]
def useDeprecatedList : DeprecatedList Nat := DeprecatedList.cons 1 DeprecatedList.nil

-- Test deprecated mutual inductive types
mutual
  @[deprecated "Use Tree instead" (since:="2025-06-23")]
  inductive DeprecatedTree (α : Type) where
    | leaf : α → DeprecatedTree α
    | node : DeprecatedForest α → DeprecatedTree α

  @[deprecated "Use Forest instead" (since:="2025-06-23")]
  inductive DeprecatedForest (α : Type) where
    | empty : DeprecatedForest α
    | cons : DeprecatedTree α → DeprecatedForest α → DeprecatedForest α
end

-- Test using deprecated mutual inductive types

@[deprecated "Use Tree instead" (since:="2025-06-23")]
def useDeprecatedTree : DeprecatedTree Nat :=
  DeprecatedTree.node (DeprecatedForest.cons (DeprecatedTree.leaf 42) DeprecatedForest.empty)
