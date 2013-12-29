Import cast
Variable A : Type
Variable B : Type
Variable A' : Type
Variable B' : Type
Axiom H : (A -> B) = (A' -> B')
Variable a : A
Check DomInj H
Theorem BeqB' : B = B' := RanInj H a
SetOption pp::implicit true
Show DomInj H
Show RanInj H a
