def foo (_ : Nat) : Nat := 10

example : foo x = 8 + 2 := by
  fail_if_success simp only
  simp only [Nat.reduceAdd]
  rw [foo]


example : foo x = 8 + 2 := by
  fail_if_success simp [-Nat.reduceAdd]
  simp only [Nat.reduceAdd]
  rw [foo]

example (h : 0 = x) : (-2).toNat = x := by
  simp
  guard_target =ₛ 0 = x
  assumption

example (h : 1 = x) : (1 : Int).toNat = x := by
  simp
  guard_target =ₛ 1 = x
  assumption
