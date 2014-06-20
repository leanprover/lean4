abbreviation Bool : Type.{1} := Type.{0}
variables a b c : Bool
axiom Ha : a
axiom Hb : b
axiom Hc : c
check have H1 : a, from Ha,
      then have H2 : a, from H1,
      have H3 : a, from H2,
      then have H4 : a, from H3,
      H4