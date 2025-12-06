example : (2 / 3 : Rat) ≤ (0.67 : Rat) := by  grind
example : (1.2 : Rat) ≤ (1.21 : Rat) := by grind
example : (2 / 3 : Rat) ≤ (67 / 100 : Rat) := by grind
example : (2 / 3 : Rat) ≤ (67 * 10 ^ (-2) : Rat) := by grind
example : (2 / 3 : Rat) ≤ (67 / 10 ^ 2 : Rat) := by grind
example : (2 / 3 : Rat) ≤ (67 / 10 ^ (2:Int) : Rat) := by grind
example : (1.2345 : Rat) ≤ (1.2346 : Rat) := by grind
example : (1.2345 : Rat) ≤ (1.234501 : Rat) := by grind
example : (2.3 : Rat) ≤ (4.5 : Rat) := by grind
example : (2.3 : Rat) ≤ (5/2 : Rat) := by grind

open Lean Grind Std
variable [LE α] [LT α] [LawfulOrderLT α] [Field α] [OfScientific α] [LawfulOfScientific α] [IsLinearOrder α] [OrderedRing α]
example : (2 / 3 : α) ≤ (0.67 : α) := by  grind
example : (1.2 : α) ≤ (1.21 : α) := by grind
example : (2 / 3 : α) ≤ (67 / 100 : α) := by grind
example : (1.2345 : α) ≤ (1.2346 : α) := by grind
example : (2.3 : α) ≤ (4.5 : α) := by grind
example : (2.3 : α) ≤ (5/2 : α) := by grind
