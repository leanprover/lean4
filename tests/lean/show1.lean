import logic
open bool eq tactic
notation H `⁻¹` := symm H --input with \sy or \-1 or \inv
notation H1 ⬝ H2 := trans H1 H2
constants a b c : bool
axiom H1 : a = b
axiom H2 : b = c
check show a = c, from H1 ⬝ H2
print "------------"
check have e1 : a = b, from H1,
      have e2 : a = c, from sorry, -- by apply eq.trans; apply e1; apply H2,
      have e3 : c = a, from e2⁻¹,
      have e4 : b = a, from e1⁻¹,
      show b = c, from e1⁻¹ ⬝ e2
