/-! # Test that safe exponentiation does not cause a panic -/

universe u

class G (A : outParam Nat) where Z : Type u

export G (Z)

/-! Define an abbrev which `reducePow` can work on -/

abbrev f (a : Nat) : Nat := 2 ^ a

variable [G (f 0)]

/-! This should not cause a panic -/

example {s : Z} : s = s := by simp only [Nat.reducePow]
