module
open Lean Grind

-- Should not produced spurious issues.
#guard_msgs (drop error, trace) in
set_option trace.grind.issues true in
example [Field α] (a b : α) : a*b + b*c = 2 → b = a⁻¹ := by
  grind
