structure Group :=
(carrier : Type) (mul : carrier → carrier → carrier) (one : carrier)

definition Group_to_Type [instance] : has_coe_to_sort Group :=
has_coe_to_sort.mk Type Group.carrier

constant g : Group.{1}
set_option pp.binder_types true

check λ a b : g, Group.mul g a b
