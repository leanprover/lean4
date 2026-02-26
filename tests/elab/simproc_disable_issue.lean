example : 2^64 = 0+x := by
  simp [-Nat.reducePow]
  guard_target =ₛ 2^64 = x
  sorry

example : 2^64 = x := by
  fail_if_success simp only
  guard_target =ₛ 2^64 = x
  sorry

example : 2^8 = x := by
  simp only [Nat.reducePow]
  guard_target =ₛ256 = x
  sorry
