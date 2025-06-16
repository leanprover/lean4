open Lean Grind
variable (R : Type u) [IntModule R]
set_option grind.debug true

example (a b : R) : a + b = b + a := by grind
example (a : R) : a + 0 = a := by grind
example (a : R) : 0 + a = a := by grind
example (a b c : R) : a + b + c = a + (b + c) := by grind
example (a : R) : 2 * a = a + a := by grind
example (a : R) : (-2 : Int) * a = -a - a := by grind
example (b c : R) : 2 * (b + c) = c + 2 * b + c := by grind
example (b c : R) : 2 * (b + c) - 3 * c + b + b = c + 5 * b - 2 * c - b := by grind
example (b c : R) : 2 * (b + c) + (-3 : Int) * c + b + b = c + (5 : Int) * b - 2 • c - b := by grind
example (b : R) : 2•b = 1•b + b := by grind

example [CommRing α] (b : α) : 2•b = 1•b + b := by grind -ring
example [CommRing α] (b : α) : 2•b = 1•b + b := by grind
