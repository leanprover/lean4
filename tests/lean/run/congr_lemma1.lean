open tactic

set_option pp.binder_types true

example : true :=
by do
  ite ← mk_const "ite",
  l   ← mk_congr_simp ite,
  trace_expr (congr_lemma.type l),
  l   ← mk_hcongr ite,
  trace_expr (congr_lemma.type l),
  constructor
