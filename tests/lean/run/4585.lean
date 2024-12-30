example (x y : Nat) : let a := (x,y); a.2 = 0 := by
  intro a
  fail_if_success simp
  guard_target =ₛ a.2 = 0
  simp +zetaDelta
  guard_target =ₛ y = 0
  sorry

example (x y : Nat) : let a := (x,y); a.2 = 0 := by
  intro a
  simp [a]
  guard_target =ₛ y = 0
  sorry
