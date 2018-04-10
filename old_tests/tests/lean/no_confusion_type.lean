namespace Ex
open nat

inductive vector (A : Type) : nat → Type
| vnil  : vector nat.zero
| vcons : Π {n : nat}, A → vector n → vector (succ n)

#check vector.no_confusion_type
constants a1 a2 : nat
constants v1 v2 : vector nat 2
constant  P     : Type
#reduce vector.no_confusion_type P (vector.vcons a1 v1) (vector.vcons a2 v2)
end Ex
