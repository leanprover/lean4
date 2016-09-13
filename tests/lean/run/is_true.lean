open nat

example : as_true (2 = (2:nat))  := trivial
example : as_false (3 = (2:nat)) := trivial
example : as_true (2 < (3:nat)) := trivial
