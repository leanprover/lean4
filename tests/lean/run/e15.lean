prelude
inductive nat : Type
| zero : nat
| succ : nat → nat
namespace nat end nat open nat

inductive list (A : Sort*)
| nil {} : list
| cons   : A → list → list
namespace list end list open list
check nil
check nil.{1}
check @nil.{1} nat
check @nil nat

check cons zero nil

inductive vector (A : Sort*) : nat → Sort*
| vnil {} : vector zero
| vcons   : forall {n : nat}, A → vector n → vector (succ n)
namespace vector end vector open vector

check vcons zero vnil
constant n : nat
check vcons n vnil

check vector.rec
