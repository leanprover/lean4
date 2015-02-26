import logic
open nat

inductive vector (A : Type) : nat → Type :=
vnil  : vector A zero |
vcons : Π {n : nat}, A → vector A n → vector A (succ n)

check vector.no_confusion_type
constants a1 a2 : num
constants v1 v2 : vector num 2
constant  P     : Type₁
eval vector.no_confusion_type P (vector.vcons a1 v1) (vector.vcons a2 v2)
