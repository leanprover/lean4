--
open nat

constant f : nat → nat
constant g : nat → nat → nat

notation A `:+1`:100000 := f A

#check g 0:+1:+1 (1:+1 + 2:+1):+1

set_option pp.notation false

#check g 0:+1:+1 (1:+1 + 2:+1):+1
