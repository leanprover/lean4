open tactic

example (b1 b2 : bool) (h : b1 = ff) : b1 && b2 = ff :=
by do h ← get_local `h,
      subst h
