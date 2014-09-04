inductive nat : Type :=
zero : nat,
succ : nat → nat

inductive vector (A : Type) : nat → Type :=
vnil  : vector A zero,
vcons : Π {n : nat}, A → vector A n → vector A (succ n)

check vector.{1}
check vnil.{1}
check vcons.{1}
check vector.rec.{1 1}
