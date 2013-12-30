Import int.
Variable g {A : Type} (a : A) : A
Variable a : Int
Variable b : Int
Axiom H1 : a = b
Axiom H2 : (g a) > 0
Theorem T1 : (g b) > 0 := SubstP (λ x, (g x) > 0) H2 H1
Show Environment 2
