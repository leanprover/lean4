universe u

structure Group :=
(carrier : Type u) (mul : carrier → carrier → carrier) (one : carrier)

instance GroupToType (g : Group) : CoeSort Group g (Type u) :=
CoeSort.mk _ g.carrier

new_frontend

variable (g : Group.{1})

#check fun (a b : g) => g.mul a b
