module

public import Accepted

/-! Unconditional targets for conditional comparison tests. -/

public section

theorem task : True := by sorry
theorem plain : True := by sorry
theorem quantified (n : Nat) : n = n := by sorry
theorem supplied : Accepted.first := by sorry
