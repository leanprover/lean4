example : (1:Nat) = 0 := by
  fail_if_success simp only
  simp only [reduceCtorEq]
  guard_target =ₛ False
  sorry

example : (1:Int) = 0 := by
  fail_if_success simp only
  sorry

example : (-1:Int) = 0 := by
  fail_if_success simp only
  simp only [reduceCtorEq]
  guard_target =ₛ False
  sorry

example : 2^10000 = 2^9999 := by
  fail_if_success simp only
  fail_if_success simp only [reduceCtorEq]
  sorry

example : 2^10000 = 2^9999 := by
  fail_if_success simp (config := Lean.Meta.Simp.neutralConfig) only
  fail_if_success simp (config := Lean.Meta.Simp.neutralConfig) only [reduceCtorEq]
  sorry
