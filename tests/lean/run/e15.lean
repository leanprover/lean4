prelude
inductive nat : Type
| zero : nat
| succ : nat → nat
namespace nat end nat open nat

inductive list (A : Type) : Type
| nil {} : list
| cons   : A → list → list
namespace list end list open list
check nil
check nil.{1}
check @nil.{1} nat
check @nil nat

check cons zero nil

inductive vector (A : Type) : nat → Type
| vnil {} : vector zero
| vcons   : forall {n : nat}, A → vector n → vector (succ n)
namespace vector end vector open vector

check vcons zero vnil
constant n : nat
check vcons n vnil

check vector.rec

definition vector_to_list {A : Type} {n : nat} (v : vector A n) : list A
:= vector.rec nil (fun (n : nat) (a : A) (v : vector A n) (l : list A), cons a l) v
