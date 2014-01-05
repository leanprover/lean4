Import Int.
Variable g {A : Type} (a : A) : A
Variable a : Int
Variable b : Int
Axiom H1 : a = b
Axiom H2 : (g a) > 0
Theorem T1 : (g b) > 0 := Subst H2 H1
print Environment 2
