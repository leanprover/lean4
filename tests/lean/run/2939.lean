def foo (x := 0) : Nat := x
example : foo x = x := by simp only [foo] -- ok
example : foo x = x := by rw [foo]
