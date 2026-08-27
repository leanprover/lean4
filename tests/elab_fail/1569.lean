def foo (x : Nat) (_ : x = 0) : Nat := x
example : foo 0 (by simp [typo]; done) = 0 := sorry
