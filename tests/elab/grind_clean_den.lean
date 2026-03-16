open Std Lean.Grind

section
variable {α : Type} [Field α] [LE α] [LT α] [LawfulOrderLT α] [IsLinearOrder α] [OrderedRing α]

example (a b : α) (h : a < b * (3⁻¹)^2) : 9 * a < b := by grind
example (a b : α) (h : a ≤ b * (3⁻¹)^2) : 9 * a ≤ b := by grind
example (a b : α) (h : a < b / 2) : 2 * a < b := by grind
example (a b : α) (h : a < b / 2) : a + a < b := by grind
example (a b : α) (h : a < b / 2) : 2 * a ≤ b := by grind
example (a b : α) (h : a < b / 2) : a + a ≤ b := by grind
example (a b : α) (h : a ≤ b / 2) : 2 * a ≤ b := by grind
example (a b : α) (h : a ≤ b / 2) : a + a ≤ b := by grind
example (a b : α) (_ : 0 ≤ a) (h : a ≤ b) : a / 7 ≤ b / 2 := by grind
example (a b : α) (_ : b < 0) (h : a < b) : (3/2) * a < (5/4) * b := by grind

example (a b : α) (h : a = b * (3⁻¹)^2) : 9 * a ≤ b := by grind
example (a b : α) (h : a = b / 2) : a + a ≤ b := by grind
example (a b : α) (h : a ≠ b) : a < b ∨ a > b := by grind
variable [NoNatZeroDivisors α]
example (a b : α) (h : a ≠ b * (3⁻¹)^2) : 9 * a < b ∨ 9 * a > b := by grind
example (a b : α) (h : a / 2 ≠ b / 9) : 9 * a < 2 * b ∨ 9 * a > 2 * b := by grind

example (a b : α) (h : a < b / (2^2 - 3/2 + -1 + 1/2)) : 2 * a < b := by grind

end

example (a b : Rat) (h : a < b * (3⁻¹)^2) : 9 * a < b := by grind
example (a b : Rat) (h : a ≤ b * (3⁻¹)^2) : 9 * a ≤ b := by grind
example (a b : Rat) (h : a < b / 2) : 2 * a < b := by grind
example (a b : Rat) (h : a < b / 2) : a + a < b := by grind
example (a b : Rat) (h : a < b / 2) : 2 * a ≤ b := by grind
example (a b : Rat) (h : a < b / 2) : a + a ≤ b := by grind
example (a b : Rat) (h : a ≤ b / 2) : 2 * a ≤ b := by grind
example (a b : Rat) (h : a ≤ b / 2) : a + a ≤ b := by grind
example (a b : Rat) (_ : 0 ≤ a) (h : a ≤ b) : a / 7 ≤ b / 2 := by grind
example (a b : Rat) (_ : b < 0) (h : a < b) : (3/2) * a < (5/4) * b := by grind
example (a b : Rat) (h : a = b * (3⁻¹)^2) : 9 * a ≤ b := by grind
example (a b : Rat) (h : a = b / 2) : a + a ≤ b := by grind
example (a b : Rat) (h : a ≠ b * (3⁻¹)^2) : 9 * a < b ∨ 9 * a > b := by grind
example (a b : Rat) (h : a / 2 ≠ b / 9) : 9 * a < 2 * b ∨ 9 * a > 2 * b := by grind
