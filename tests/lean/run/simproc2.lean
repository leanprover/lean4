def foo (_ : Nat) : Nat := 10

example : foo x = 8 + 2 := by
  fail_if_success simp only
  simp only [Nat.reduceAdd]
  rw [foo]
