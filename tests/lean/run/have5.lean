import standard
using tactic
variables a b c d : Bool
axiom Ha : a
axiom Hb : b
axiom Hc : c
print raw
  have H1 : a, by exact,
  then have H2 : b, by exact,
  have H3 : c, by exact,
  then have H4 : d, by exact,
  H4