import Int.
variable a : Int
variable n : Nat
axiom H1 : a + a + a = 10
axiom H2 : a = n
theorem T : a + n + a = 10 := Subst H1 H2
setoption pp::coercion true
setoption pp::notation false
setoption pp::implicit true
print environment 1.
