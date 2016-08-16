import algebra.group data.real
open nat

attribute [instance, priority 2]
definition foo1 : inhabited nat := inhabited.mk 10

attribute [instance, priority 1]
definition foo2 : inhabited nat := inhabited.mk 10

open algebra

attribute [instance, priority 1]
definition foo3 : inhabited nat := inhabited.mk 10

attribute [unfold 2 3]
definition foo4 (a b c : nat) := a + b + c

attribute [recursor 4]
definition natrec {C : nat → Type} (H₁ : C 0) (H₂ : Π (n : nat), C n → C (succ n)) (n : nat) : C n :=
nat.rec_on n H₁ H₂
