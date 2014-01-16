variable Vector : Nat -> Type
variable n  : Nat
variable v1 : Vector n
variable v2 : Vector (n + 0)
variable v3 : Vector (0 + n)
axiom cast {A B : TypeU} : A = B -> A -> B
axiom H1 : v1 = cast (congr2 Vector (Nat::add_zeror n)) v2
axiom H2 : v2 = cast (congr2 Vector (Nat::add_comm 0 n)) v3
