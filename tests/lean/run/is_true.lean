import data.nat
open nat

example : is_true (2 = 2)  := trivial
example : is_false (3 = 2) := trivial
example : is_true (2 < 3) := trivial
example : is_true (3 ∣ 9) := trivial
example : is_false (3 ∣ 7) := trivial
