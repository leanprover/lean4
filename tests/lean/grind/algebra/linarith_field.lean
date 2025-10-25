open Std Lean.Grind

variable {α : Type} [Field α] [LE α] [LT α] [LawfulOrderLT α] [IsLinearOrder α] [OrderedRing α]

example (a b : α) (h : a < b / 2) : 2 * a < b := by grind
example (a b : α) (h : a < b / 2) : a + a < b := by grind
example (a b : α) (h : a < b / 2) : 2 * a ≤ b := by grind
example (a b : α) (h : a < b / 2) : a + a ≤ b := by grind
example (a b : α) (h : a ≤ b / 2) : 2 * a ≤ b := by grind
example (a b : α) (h : a ≤ b / 2) : a + a ≤ b := by grind

example (a b : α) (_ : 0 ≤ a) (h : a ≤ b) : a / 7 ≤ b / 2 := by grind

example (a b : α) (_ : b < 0) (h : a < b) : (3/2) * a < (5/4) * b := by grind
