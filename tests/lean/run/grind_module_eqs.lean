open Lean Grind

example [IntModule α] (x y : α) : x - y ≠ 0 - 2*y → x + y = 0 → False := by
  grind

example [IntModule α] (x y : α) : 2*x + 2*y ≠ 0 → x + y = 0 → False := by
  grind

example [IntModule α] (x y : α) : 2*x + 2*y ≠ 0 → 2*x + 2*y = 0 → False := by
  grind

example [IntModule α] [NoNatZeroDivisors α] (x y : α) : x + y ≠ 0 → 2*x + 2*y = 0 → False := by
  grind

example [IntModule α] [NoNatZeroDivisors α] (x y z : α) : x + y + z ≠ 0 → 2*x + 3*y = 0 → y = 2*z → False := by
  grind

example [IntModule α] [NoNatZeroDivisors α] (x y z : α) : x + y + z ≠ 0 → -3*y = 2*x → y = 2*z → False := by
  grind

example [IntModule α] (x y : α) : x + y = 0 → x - y = 0 - 2*y := by
  grind

example [IntModule α] (x y : α) : x + y = 0 → 2*x + 2*y = 0 := by
  grind

example [IntModule α] (x y : α) : 2*x + 2*y = 0 → 2*x = 0 - 2*y := by
  grind

example [IntModule α] [NoNatZeroDivisors α] (x y : α) : 2*x + 2*y = 0 → x = -y := by
  grind

example [IntModule α] [NoNatZeroDivisors α] (x y z : α) : 2*x + 3*y = 0 → y = 2*z → x + y + z = 0 := by
  grind

example [IntModule α] [NoNatZeroDivisors α] (x y z : α) : -3*y = 2*x → y = 2*z → x + y + z = 0 := by
  grind
