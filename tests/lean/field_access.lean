#check list.map

variable l : list nat

#check l^.1 -- Error l is not a structure

#check (1, 2)^.5 -- Error insufficient fields

example (l : list nat) : list nat :=
l^.forr (λ x, x + 1) -- Error there is no list.forr

example (A : Type) (a : A) : A :=
a^.symm -- Error type of 'a' is not a constant application

example (l : list nat) : list nat :=
l^.for (λ x, x + 1)

example (l : list nat) : list nat :=
l^.for (λ x, x + 1)

example (a b : nat) (h : a = b) : b = a :=
h^.symm

example (a b : nat) (h : a = b) : b = a :=
h^.symm
