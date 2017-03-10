set_option pp.all true

structure p1 :=
(x : nat)

#check @p1.induction_on

inductive p2
| mk : nat → p2

#check @p2.induction_on
