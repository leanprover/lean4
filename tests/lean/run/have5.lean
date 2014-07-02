import standard
variables a b c d : Bool
axiom Ha : a
axiom Hb : b
axiom Hc : c
print raw
  have H1 : a, by exact_tac,
  then have H2 : b, by exact_tac,
  have H3 : c, by exact_tac,
  then have H4 : d, by exact_tac,
  H4