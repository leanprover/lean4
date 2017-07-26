open tactic

universe variables u

axiom app : Π {α : Type u} {n m : nat}, vector α m → vector α n → vector α (m+n)

example (n1 n2 n3 : nat) (v1 w1 : vector nat n1) (w1' : vector nat n3) (v2 w2 : vector nat n2) :
        n1 = n3 → v1 = w1 → w1 == w1' → v2 = w2 → app v1 v2 == app w1' w2 :=
by cc

example (n1 n2 n3 : nat) (v1 w1 : vector nat n1) (w1' : vector nat n3) (v2 w2 : vector nat n2) :
        n1 == n3 → v1 = w1 → w1 == w1' → v2 == w2 → app v1 v2 == app w1' w2 :=
by cc

example (n1 n2 n3 : nat) (v1 w1 v : vector nat n1) (w1' : vector nat n3) (v2 w2 w : vector nat n2) :
        n1 == n3 → v1 = w1 → w1 == w1' → v2 == w2 → app w1' w2 == app v w → app v1 v2 = app v w :=
by cc
