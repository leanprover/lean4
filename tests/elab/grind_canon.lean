structure A where

class B (α : Type u) where
  data : Nat

instance (priority := low) instBA : B A where
  data := 0

@[grind =]
theorem data_eq : B.data A = 0 := rfl

class C (α : Type u) extends B α where

instance instCA : C A where

example : instCA.toB = instBA := by
  with_reducible_and_instances rfl

example : B.data A = 0 := by grind
