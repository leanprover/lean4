open tactic

set_option pp.all true

example (a b : nat) : a = b → a = a :=
by do
  intro "H",
  eqc : expr ← mk_const "eq",
  A   ← mk_mvar,
  m₁  ← mk_mvar,
  m₂  ← mk_mvar,
  e   ← return (eqc A m₁ m₂),
  trace "pattern: ",
  trace_expr e,
  H   ← get_local "H",
  Ht  ← infer_type H,
  trace "term to unify: ",
  trace_expr Ht,
  unify Ht e,
  trace "unification results using whnf: ",
  whnf A >>= trace_expr,
  whnf m₁ >>= trace_expr,
  whnf m₂ >>= trace_expr,
  trace "unification results using get_assignment: ",
  get_assignment A >>= trace_expr,
  get_assignment m₁ >>= trace_expr,
  get_assignment m₂ >>= trace_expr,
  mk_app ("eq" <.> "refl") [m₁] >>= exact
