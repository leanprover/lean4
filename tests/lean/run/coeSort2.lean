

universe u

structure Group :=
(carrier : Type u) (mul : carrier → carrier → carrier) (one : carrier)

instance GroupToType : CoeSort Group (Type u) :=
CoeSort.mk (fun g => g.carrier)

variable (g : Group.{1})

#check fun (a b : g) => g.mul a b
