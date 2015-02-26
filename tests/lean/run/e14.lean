prelude
inductive nat : Type :=
| zero : nat
| succ : nat → nat
namespace nat end nat open nat

inductive list (A : Type) : Type :=
| nil {} : list A
| cons   : A → list A → list A
definition nil := @list.nil
definition cons := @list.cons

check nil
check nil.{1}
check @nil.{1} nat
check @nil nat

check cons nat.zero nil

inductive vector (A : Type) : nat → Type :=
| vnil {} : vector A zero
| vcons   : forall {n : nat}, A → vector A n → vector A (succ n)
namespace vector end vector open vector

check vcons zero vnil
constant n : nat
check vcons n vnil

check vector.rec

definition vector_to_list {A : Type} {n : nat} (v : vector A n) : list A
:= vector.rec (@nil A) (fun (n : nat) (a : A) (v : vector A n) (l : list A), cons a l) v

attribute vector_to_list [coercion]

constant f : forall {A : Type}, list A → nat

check f (cons zero nil)
check f (vcons zero vnil)
