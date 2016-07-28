constant boo.f : nat → bool
constant bla.f : nat → nat

open boo bla

#elab f 1

set_option pp.full_names true

#elab (f 1 : nat)

#elab (f 1 : bool)

set_option pp.full_names false

#elab (f 1 : string)
