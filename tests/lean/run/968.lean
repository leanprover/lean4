variables (A : Type) [inhabited A]

definition f (a : A) : A := a

check @f nat nat.is_inhabited

structure foo :=
(a : A)

check @foo nat nat.is_inhabited

inductive bla :=
| mk : A → bla

check @bla nat nat.is_inhabited
