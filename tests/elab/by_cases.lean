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
error: failed to synthesize instance of type class
  Decidable p

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example (p : Prop) : True := by
  if p then exact decide p else trivial
