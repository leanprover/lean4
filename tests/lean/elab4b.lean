definition foo.f {A : Type*} {B : Type*} (a : A) (b : B) : A := a

definition boo.f (a : nat) (b : nat) (c : nat) := a + b + c

definition bla.f (a b c d : bool) := a

open boo foo bla

#check f 0 1 2 3

#check f 0 1

#check f tt ff
