definition foo.f {A : Type} {B : Type} (a : A) (b : B) : A := a

definition boo.f (a : nat) (b : nat) (c : nat) := a + b + c

definition bla.f (a b c d : bool) := a

open boo foo bla

set_option pp.full_names true

#elab f 0 1 2

#elab f 0 1 2 3

#elab f 0 1

#elab f tt 2

#elab f tt ff tt

#elab f tt ff

#elab @foo.f _ _ 0 1
