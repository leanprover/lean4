import data.nat
open nat

example : is_true (2 = (2:nat))  := trivial
example : is_false (3 = (2:nat)) := trivial
example : is_true (2 < (3:nat)) := trivial
example : is_true (3 ∣ (9:nat)) := trivial
example : is_false (3 ∣ (7:nat)) := trivial
