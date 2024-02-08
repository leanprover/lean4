example : True := by
  if 1 + 1 = 2 then _ else ?_
  case pos => trivial
  fail_if_success case neg => contradiction
  · contradiction

example (p : Prop) : True := by
  if p then ?foo else trivial
  case foo => trivial
