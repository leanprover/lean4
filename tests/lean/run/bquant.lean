import data.nat.bquant
open nat

example : is_true (∀ x, x ≤ 4 → x ≠ 6) :=
trivial

example : is_false (∀ x, x ≤ 5 → ∀ y, y < x → y * y ≠ x) :=
trivial

example : is_true (∀ x, x < 5 → ∃ y, y ≤ x + 5 ∧ y = 2*x) :=
trivial
