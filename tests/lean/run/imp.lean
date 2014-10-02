constant N : Type.{1}
constants a b c : N
constant f : forall {a b : N}, N → N

check f
check @f
check @f a
check @f a b
check @f a b c

definition l1 : N → N → N → N := @f
definition l2 : N → N → N := @f a
definition l3 : N → N := @f a b
definition l4 : N := @f a b c

constant g : forall ⦃a b : N⦄, N → N

check g
check g a
check @g
check @g a
check @g a b
check @g a b c

definition l5 : N → N → N → N := @g
definition l6 : N → N → N := @g a
definition l7 : N → N := @g a b
definition l8 : N := @g a b c
definition l9 : N → N → N → N := g
