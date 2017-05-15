open tactic

#check
λ (A : Type) (a b c d : A) (H1 : a = b) (H2 : c = b) (H3 : d = c),
have Hac : a = c, by do {
 h  ← get_local `H2,
 hs ← mk_app `eq.symm [h],
 x  ← to_expr ```(eq.trans H1 %%hs),
 exact x },
show a = d, by do {
  x ← to_expr ```(
    have aux : a = c, from Hac,
    have c = d, by do { symmetry, assumption },
    show a = d, by do {
      get_local `Hac >>= clear,
      get_local `H1 >>= clear,
      trace "NESTED CALL:",
      trace_state,
      transitivity,
      get_local `aux >>= exact,
      assumption }),
  trace "-----------",
  trace_state,
  exact x }
