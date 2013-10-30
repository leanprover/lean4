

Variable Vector : Nat -> Type
Variable n  : Nat
Variable v1 : Vector n
Variable v2 : Vector (n + 0)
Variable v3 : Vector (0 + n)
Axiom H1 : v1 == v2
Axiom H2 : v2 == v3
Check TransExt H1 H2
Set pp::implicit true
Check TransExt H1 H2
