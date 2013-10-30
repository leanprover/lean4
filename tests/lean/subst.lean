Variable a : Int
Variable n : Nat
Axiom H1 : a + a + a = 10
Axiom H2 : a = n
Theorem T : a + n + a = 10 := Subst H1 H2
Set pp::coercion true
Set pp::notation false
Set pp::implicit true
Show Environment 1.
