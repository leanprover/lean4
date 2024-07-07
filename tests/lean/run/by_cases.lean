example : True := by
  if 1 + 1 = 2 then _ else ?_
  case pos => trivial
  fail_if_success case neg => contradiction
  · contradiction

example (p : Prop) : True := by
  if p then ?foo else trivial
  case foo => trivial

/-! Should not accidentally leak `open Classical` into branches. -/

/--
error: failed to synthesize
  Decidable p
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example (p : Prop) : True := by
  if p then exact decide p else trivial
