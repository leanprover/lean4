import algebra.ring
set_option pp.all true

constant int : Type₁
constant int_comm_ring : comm_ring int
attribute int_comm_ring [instance]

check 3

check Type

check Prop

check int

check (2 : int)

check eq.subst
