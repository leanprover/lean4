open tactic

set_option pp.implicit true

example (a b c d : nat) (f : nat → nat → nat) : a = b → b = c → d + (if b > 0 then a else b) = 0 → f (b + b) b ≠ f (a + c) c → false :=
by do intros,
      s ← cc_state.mk_using_hs,
      s^.pp >>= trace,
      t₁ ← to_expr `(f (b + b) b),
      t₂ ← to_expr `(f (a + c) c),
      b  ← to_expr `(b),
      d  ← to_expr `(d),
      guard (s^.inconsistent),
      guard (s^.eqc_size b = 3),
      guard (not (s^.in_singlenton_eqc b)),
      guard (s^.in_singlenton_eqc d),
      trace ">>> Equivalence roots",
      trace s^.roots,
      trace ">>> b's equivalence class",
      trace (s^.eqc_of b),
      pr ← s^.eqv_proof t₁ t₂,
      note `h pr,
      contradiction
