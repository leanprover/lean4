constant boo.f : nat → bool
constant bla.f : nat → nat

open boo bla

#check f 1

set_option pp.full_names true

#check (f 1 : nat)

#check (f 1 : bool)

set_option pp.full_names false

#check (f 1 : string)
