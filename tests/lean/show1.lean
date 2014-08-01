import standard
using bool eq_proofs tactic

variables a b c : bool
axiom H1 : a = b
axiom H2 : b = c

check show a = c, from H1 ⬝ H2
print "------------"
check have e1 [fact] : a = b, from H1,
      have e2 : a = c, by apply trans; apply e1; apply H2,
      have e3 : c = a, from e2⁻¹,
      have e4 [fact] : b = a, from e1⁻¹,
      show b = c, from e1⁻¹ ⬝ e2
