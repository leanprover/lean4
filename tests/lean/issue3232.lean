inductive foo {n : Nat} : Prop

-- Check that the error message will print the types with implicit arguments shown
example (h : @foo 42) : @foo 23 := by
  apply h

example : (1 : Nat) = 1 := by
  apply (rfl : (1 : Int) = 1)

example : PUnit.{0} = PUnit.{0} := by
  apply Eq.refl PUnit.{1} -- TODO: addPPExplicitToExposeDiff is not handling this yet
