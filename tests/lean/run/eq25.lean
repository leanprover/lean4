inductive N :=
| O : N
| S : N → N

definition Nat := N

open N

definition add1 : Nat → Nat → Nat
| add1 O     b := b
| add1 (S a) b := S (add1 a b)
