import data.nat
open algebra nat

definition lemma1 (a b : nat) : a + b + 0 = b + a :=
by blast

print lemma1

definition lemma2 (a b c : nat) : a + b + 0 + c + a + a + b = 0 + 0 + c + a + b + a + a + b :=
by blast

print lemma2
