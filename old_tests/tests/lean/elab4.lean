definition foo.f {A : Type*} {B : Type*} (a : A) (b : B) : A := a

definition boo.f (a : nat) (b : nat) (c : nat) := a + b + c

definition bla.f (a b c d : bool) := a

open boo foo bla

set_option pp.full_names true

#check f 0 1 2

#check f 0 1 2 3

#check f 0 1

#check f tt 2

#check f tt ff tt

#check f tt ff

#check @foo.f _ _ 0 1
