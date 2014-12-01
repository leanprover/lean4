prelude
definition Prop : Type.{1} := Type.{0}
constants a b c : Prop
axiom Ha : a
axiom Hb : b
axiom Hc : c
check have H1 : a, from Ha,
      have H2 : a, using H1, from H1,
      H2
