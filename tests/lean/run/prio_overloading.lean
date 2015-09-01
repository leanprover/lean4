import algebra.group data.real
open nat

definition foo1 [instance] [priority 2] : inhabited nat := inhabited.mk 10

definition foo2 [instance] [priority 1] : inhabited nat := inhabited.mk 10

open algebra

definition foo3 [instance] [priority 1] : inhabited nat := inhabited.mk 10

definition foo4 [unfold 2 3] (a b c : nat) := a + b + c

definition natrec [recursor 4] {C : nat → Type} (H₁ : C 0) (H₂ : Π (n : nat), C n → C (succ n)) (n : nat) : C n :=
nat.rec_on n H₁ H₂
