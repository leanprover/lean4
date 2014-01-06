import Int.
variable g {A : Type} (a : A) : A
variable a : Int
variable b : Int
axiom H1 : a = b
axiom H2 : (g a) > 0
theorem T1 : (g b) > 0 := subst H2 H1
print environment 2
