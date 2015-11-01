import algebra.ring

variables a b c : nat
variables H1 : a = b
variables H2 : b = c
set_option pp.all true

#app_builder eq.refl (a)
#app_builder eq.trans (H1, H2)
#app_builder eq.symm (H1)

open algebra
variables A : Type
variables [s : comm_ring A]
variables x y : A

#app_builder eq.refl (s)
#app_builder eq.refl (x)
