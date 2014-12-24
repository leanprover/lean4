import data.prod
open nat prod

set_option pp.universes true

definition tuple (A : Type) (n : nat) : Type :=
nat.rec_on n A (λ n r, r × A)

check @tuple
