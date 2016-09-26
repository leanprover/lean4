open nat

def below (n : nat) : nat → Prop :=
λ i, i < n

def f {n : nat} (v : subtype (below n)) : nat :=
v + 1
