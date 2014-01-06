import cast
variable A : Type
variable B : Type
variable A' : Type
variable B' : Type
axiom H : (A -> B) = (A' -> B')
variable a : A
check dominj H
theorem BeqB' : B = B' := raninj H a
set::option pp::implicit true
print dominj H
print raninj H a
