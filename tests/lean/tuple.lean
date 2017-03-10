open nat prod

set_option pp.universes true

definition {u} tuple (A : Type (u+1)) (n : nat) : Type (u+1)  :=
nat.rec_on n A (λ n r, r × A)

#check @tuple
