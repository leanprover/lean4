prelude
inductive nat : Type :=
| zero : nat
| succ : nat → nat

check nat
check nat.rec.{1}
