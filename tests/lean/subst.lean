Import Int.
Variable a : Int
Variable n : Nat
Axiom H1 : a + a + a = 10
Axiom H2 : a = n
Theorem T : a + n + a = 10 := Subst H1 H2
SetOption pp::coercion true
SetOption pp::notation false
SetOption pp::implicit true
print Environment 1.
