open tactic

example : size_of [tt, tt] < size_of [tt, ff, tt] :=
dec_trivial

example : size_of [tt, tt] = size_of [ff, ff] :=
dec_trivial

example : size_of (3:nat) < size_of ([3] : list nat) :=
dec_trivial
