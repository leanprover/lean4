example (n t : Nat) : 1 ^ (n / 3) * 2 ^ t = 2 ^ t := by grind

example (n t : Nat) : (1 : Int) ^ (n / 3) * 2 ^ t = 2 ^ t := by grind

open Lean Grind

example (x y : Nat) : x + y = 1 → y + x = 1 := by
  grind -cutsat -linarith

example (x y : Nat) : x^2*y = 1 → x*y^2 = y → y*x = 1 := by
  grind -cutsat -linarith

example (x y : Nat) : x + y = 1 → x + z + y = 2 → z = 0 → False := by
  grind -cutsat -linarith

example [CommSemiring α] [AddRightCancel α] [IsCharP α 0] (x y z : α)
    : x + y = 1 → x + z + y = 2 → z = 0 → False := by
  grind -cutsat -linarith

example (x y : Nat) : x^2*y = 1 → x*y^2 = y → y*x = 1 := by
  grind

example [CommSemiring α] [AddRightCancel α] (x y : α) : x^2*y = 1 → x*y^2 = y → y*x = 1 := by
  grind -cutsat -linarith

example [CommSemiring α] [AddRightCancel α] (x y : α) : x^2*y = 1 → x*y^2 = y → y*x = 1 := by
  grind

example [CommSemiring α] [AddRightCancel α] [IsCharP α 0] (x y : α) : x^2*y = 1 → x*y^2 = y → x + y = 1 → False := by
  grind
