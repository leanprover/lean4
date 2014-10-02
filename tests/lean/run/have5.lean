import logic
open tactic
constants a b c d : Prop
axiom Ha : a
axiom Hb : b
axiom Hc : c
print raw
  have H1 : a, by assumption,
  then have H2 : b, by assumption,
  have H3 : c, by assumption,
  then have H4 : d, by assumption,
  H4
