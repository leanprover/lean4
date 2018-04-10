variables (A : Type) [inhabited A]

definition f (a : A) : A := a

#check @f nat nat.inhabited

structure foo :=
(a : A)

#check @foo nat nat.inhabited

inductive bla
| mk : A → bla

#check @bla nat nat.inhabited
