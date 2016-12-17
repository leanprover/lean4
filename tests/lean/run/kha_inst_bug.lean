open nat

example (a b : ℕ) : a - b = a - min a b :=
if h : a ≥ b then by rw [min_eq_right h]
else by rw [sub_eq_zero_of_le (le_of_not_ge h), min_eq_left (le_of_not_ge h), nat.sub_self]
