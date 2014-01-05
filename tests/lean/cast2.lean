import cast
variable A : Type
variable B : Type
variable A' : Type
variable B' : Type
axiom H : (A -> B) = (A' -> B')
variable a : A
check DomInj H
theorem BeqB' : B = B' := RanInj H a
setoption pp::implicit true
print DomInj H
print RanInj H a
