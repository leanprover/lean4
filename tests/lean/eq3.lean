import heq
variable Vector : Nat -> Type
variable n  : Nat
variable v1 : Vector n
variable v2 : Vector (n + 0)
variable v3 : Vector (0 + n)
axiom H1 : v1 == v2
axiom H2 : v2 == v3
check htrans H1 H2
