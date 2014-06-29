abbreviation Bool : Type.{1} := Type.{0}
variables a b c d : Bool
axiom Ha : a
axiom Hb : b
axiom Hc : c
print raw
  have H1 : a, by id,
  then have H2 : b, by id,
  have H3 : c, by id,
  then have H4 : d, by id,
  H4