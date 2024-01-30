inductive foo {n : Nat} : Prop

-- Check that the error message will print the types with implicit arguments shownx
example (h : @foo 42) : @foo 23 := by
  apply h
