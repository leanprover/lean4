open Lean Grind

example [CommRing α] (a : α) : a^0 = 1 := by
  grind

example [CommSemiring α] [AddRightCancel α] (a : α) : a^0 = 1 := by
  grind
