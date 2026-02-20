example (h : 12 = x) : 10 + 2 = x := by
  simp
  guard_target =ₛ 12 = x
  assumption

attribute [-simp] Nat.reduceAdd

example (h : 12 = x) : 10 + 2 = x := by
  fail_if_success simp
  simp [Nat.reduceAdd]
  guard_target =ₛ 12 = x
  assumption
