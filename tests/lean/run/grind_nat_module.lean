open Lean Grind
variable (M : Type) [NatModule M] [AddRightCancel M]

example (x y : M) : 2 • x + 3 • y + x = 3 • (x + y) := by
  grind
