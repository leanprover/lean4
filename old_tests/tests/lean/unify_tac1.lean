open tactic

example (A : Type) (a : A) (p : A → Prop) (H : p a) : ∃ x, p x :=
by do
  constructor,
  tgt ← target,
  t   ← get_local `H >>= infer_type,
  unify tgt t, -- Succeeds unifying p a =?= p ?m_1
  assumption

example (A : Type) (a : A) (p : A → Prop) (H : p a) : ∃ x, p x :=
by do
  econstructor,
  tgt ← target,
  t   ← get_local `H >>= infer_type,
  is_def_eq tgt t, -- Fails at p a =?= p ?m_1
  assumption

example (a : nat) : true :=
by do
  t1 ← to_expr ```(nat.succ a),
  t2 ← to_expr ```(a + 1),
  is_def_eq t1 t2, -- Succeeds
  constructor
