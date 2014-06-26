inductive nat : Type :=
| zero : nat
| succ : nat → nat

inductive list (A : Type) : Type :=
| nil  : list A
| cons : A → list A → list A

check nil
check nil.{1}
check @nil.{1} nat
check @nil nat

check cons zero nil

inductive vector (A : Type) : nat → Type :=
| vnil  : vector A zero
| vcons : forall {n : nat}, A → vector A n → vector A (succ n)

check vcons zero vnil
variable n : nat
check vcons n vnil

check vector_rec

definition vector_to_list {A : Type} {n : nat} (v : vector A n) : list A
:= vector_rec nil (fun n a v l, cons a l) v

