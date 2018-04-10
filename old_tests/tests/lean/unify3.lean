open tactic

set_option pp.all true

example (a b : nat) : a = b → a = a :=
by do
  intro `H,
  eqc : expr ← mk_const `eq,
  A   ← mk_mvar,
  m₁  ← mk_mvar,
  m₂  ← mk_mvar,
  e   ← return (expr.app_of_list eqc [A, m₁, m₂]),
  trace "pattern: ",
  trace e,
  H   ← get_local `H,
  Ht  ← infer_type H,
  trace "term to unify: ",
  trace Ht,
  unify Ht e,
  trace "unification results using whnf: ",
  whnf A >>= trace,
  whnf m₁ >>= trace,
  whnf m₂ >>= trace,
  trace "unification results using get_assignment: ",
  get_assignment A >>= trace,
  get_assignment m₁ >>= trace,
  get_assignment m₂ >>= trace,
  mk_app `eq.refl [m₁] >>= exact
