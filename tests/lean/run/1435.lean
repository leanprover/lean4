class LinearOrder (α : Type _) extends LE α, LT α

theorem le_of_not_gt [LinearOrder α] {a b : α} : ¬ a > b → a ≤ b := sorry

instance : LinearOrder Nat where
  lt := Nat.lt
  le := Nat.le

example (a b : Nat) (h : ¬a < b) : b ≤ a := by
  have := le_of_not_gt h
  exact this
