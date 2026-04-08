open BitVec

example : (5 : Fin 4) = x := by
  simp
  guard_target =ₛ 1 = x
  sorry

example : (1 : Fin 4) = x := by
  fail_if_success simp
  guard_target =ₛ 1 = x
  sorry

example : 17#4 = x := by
  simp
  guard_target =ₛ  1#4 = x
  sorry

example : (17 : BitVec 4) = x := by
  simp
  guard_target =ₛ  1#4 = x
  sorry
