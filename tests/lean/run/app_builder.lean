import algebra.ring

variables a b c : nat
variables H1 : a = b
variables H2 : b = c
set_option pp.all true

#app_builder eq.refl (a)
#app_builder eq.trans (H1, H2)
#app_builder eq.symm (H1)

open algebra nat
universe l
constant A : Type.{l}
constant s : comm_ring A
attribute s [instance]
variables x y : A

#app_builder eq.refl (s)
#app_builder eq.refl (x)
#app_builder add (x, y)
#app_builder add (a, b)
#app_builder mul (a, b)
#app_builder sub (x, y)
