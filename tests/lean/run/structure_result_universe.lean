structure foo1 (A : Type) : Type :=
(elt : A)

structure {u} foo2 (A : Type u) : Type (u+1) :=
(val : A)

structure {u} foo3 (A : Type u) : Type (max u 1) :=
(val : A)

universe variable u

structure foo4 (A : Type u) : Type (max u 1) :=
(val : A)

check foo1
check foo2
check foo3
check foo4
