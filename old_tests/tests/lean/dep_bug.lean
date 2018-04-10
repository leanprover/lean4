open tactic



example (a b c : nat) (H : c = b) : a + c = a + b :=
by do
  N ← to_expr ``(nat),
  define `v N,
  trace_state,
  trace  "------------",
  to_expr ```(a + b) >>= exact,
  trace_state,
  trace "------------",
  get_local `H >>= subst,
  trace_state,
  to_expr ```(eq.refl v) >>= exact
