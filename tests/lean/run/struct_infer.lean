import data.nat.basic
open nat
namespace foo
definition associative {A : Type} (op : A → A → A) := ∀a b c, op (op a b) c = op a (op b c)

structure semigroup [class] (A : Type) :=
mk {} :: (mul: A → A → A) (mul_assoc : associative mul)

definition nat_semigroup [instance] : semigroup nat :=
semigroup.mk nat.mul nat.mul_assoc

example (a b c : nat) : (a * b) * c = a * (b * c) :=
semigroup.mul_assoc a b c

structure semigroup2 (A : Type) :=
mk () :: (mul: A → A → A) (mul_assoc : associative mul)

definition s := semigroup2.mk nat nat.mul nat.mul_assoc

example (a b c : nat) : (a * b) * c = a * (b * c) :=
semigroup2.mul_assoc nat s a b c
end foo
