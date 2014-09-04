inductive nat : Type :=
zero : nat,
succ : nat → nat

inductive list (A : Type) : Type :=
nil {} : list A,
cons   : A → list A → list A

check nil
check nil.{1}
check @nil.{1} nat
check @nil nat

check cons zero nil

inductive vector (A : Type) : nat → Type :=
vnil {} : vector A zero,
vcons   : forall {n : nat}, A → vector A n → vector A (succ n)

check vcons zero vnil
variable n : nat
check vcons n vnil

check vector.rec

definition vector_to_list {A : Type} {n : nat} (v : vector A n) : list A
:= vector.rec (@nil A) (fun (n : nat) (a : A) (v : vector A n) (l : list A), cons a l) v

coercion vector_to_list

variable f : forall {A : Type}, list A → nat

check f (cons zero nil)
check f (vcons zero vnil)
