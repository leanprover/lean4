open tactic

set_option pp.binder_types true

example : true :=
by do
  ite ← mk_const `ite,
  l   ← mk_congr_lemma_simp ite,
  trace (congr_lemma.type l),
  l   ← mk_hcongr_lemma ite,
  trace (congr_lemma.type l),
  constructor
