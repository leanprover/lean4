open tactic

notation `dec_trivial` := of_as_true (by triv)

example : sizeof [tt, tt] < sizeof [tt, ff, tt] :=
dec_trivial

example : sizeof [tt, tt] = sizeof [ff, ff] :=
dec_trivial

example : sizeof (3:nat) < sizeof ([3] : list nat) :=
dec_trivial
