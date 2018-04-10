constant N : Type.{1}
constants a b c : N
constant f : forall {a b : N}, N → N

#check f
#check @f
#check @f a
#check @f a b
#check @f a b c

noncomputable definition l1 : N → N → N → N := @f
noncomputable definition l2 : N → N → N := @f a
noncomputable definition l3 : N → N := @f a b
noncomputable definition l4 : N := @f a b c

constant g : forall ⦃a b : N⦄, N → N

#check g
#check g a
#check @g
#check @g a
#check @g a b
#check @g a b c

noncomputable definition l5 : N → N → N → N := @g
noncomputable definition l6 : N → N → N := @g a
noncomputable definition l7 : N → N := @g a b
noncomputable definition l8 : N := @g a b c
noncomputable definition l9 : N → N → N → N := g
