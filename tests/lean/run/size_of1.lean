exit -- TODO(Leo): enable this test after we have sizeof instance generation in the inductive module
open tactic

example : sizeof [tt, tt] < sizeof [tt, ff, tt] :=
dec_trivial

example : sizeof [tt, tt] = sizeof [ff, ff] :=
dec_trivial

example : sizeof (3:nat) < sizeof ([3] : list nat) :=
dec_trivial
