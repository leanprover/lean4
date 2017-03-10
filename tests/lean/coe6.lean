universe variables u
structure Group :=
(carrier : Type u) (mul : carrier → carrier → carrier) (one : carrier)

attribute [instance]
definition Group_to_Type : has_coe_to_sort Group :=
{ S := Type u, coe := λ g, g~>carrier }

constant g : Group.{1}
set_option pp.binder_types true

#check λ a b : g, Group.mul g a b
