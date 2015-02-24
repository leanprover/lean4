inductive N :=
O : N,
S : N → N

definition Nat := N

open N

definition add : Nat → Nat → Nat,
add O     b := b,
add (S a) b := S (add a b)
