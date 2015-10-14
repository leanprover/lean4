import data.num
set_option pp.notation false
set_option pp.implicit true

constant N : Type.{1}
constant z : N
constant o : N
constant a : N

notation 0 := z
notation 1 := o

check a = 0
check 2 = 1
check (2:num) = 1
