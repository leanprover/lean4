prelude
inductive nat : Type
| zero : nat
| succ : nat → nat
namespace nat end nat open nat

inductive {u} list (A : Type u) : Type u
| nil {} : list
| cons   : A → list → list
namespace list end list open list

check nil
check nil.{0}
check @nil.{0} nat
check @nil nat

check cons zero nil

inductive {u} vector (A : Type u) : nat → Type u
| vnil {} : vector zero
| vcons   : forall {n : nat}, A → vector n → vector (succ n)
namespace vector end vector open vector

check vcons zero vnil
constant n : nat
check vcons n vnil

check vector.rec
