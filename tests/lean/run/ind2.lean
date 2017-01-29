prelude
inductive nat : Type
| zero : nat
| succ : nat → nat
namespace nat end nat open nat

inductive {u} vector (A : Type u) : nat → Type u
| vnil  : vector zero
| vcons : Π {n : nat}, A → vector n → vector (succ n)
namespace vector end vector open vector
check vector.{1}
check vnil.{1}
check vcons.{1}
check vector.rec.{1 1}
