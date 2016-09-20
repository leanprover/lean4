inductive N
| O : N
| S : N → N

definition Nat := N

open N

definition add1 : Nat → Nat → Nat
| O     b := b
| (S a) b := S (add1 a b)
