inductive nat : Type :=
zero : nat,
succ : nat → nat

check nat
check nat_rec.{1}