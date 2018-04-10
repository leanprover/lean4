open tactic
set_option pp.all true

example (F : nat → Π (n : nat), (λ (u : nat), nat → nat) n) : true :=
by do
  ⟨t, p, _⟩ ← i_to_expr ```(F 0 0) >>= mk_specialized_congr_lemma,
  trace t,
  trace p,
  type_check p,
  constructor


example (F : nat → Π (n : nat), (nat.cases_on n nat (λ _, nat) : Type)) : true :=
by do
  ⟨t, p, _⟩ ← i_to_expr ```(F 0 0) >>= mk_specialized_congr_lemma,
  trace t,
  trace p,
  type_check p,
  constructor

inductive unit' | star

lemma T (x : unit') (e : x = unit'.star) (F : nat → unit') :
  @unit'.rec (λ (u : unit'), nat → unit') F x = F :=
by simp only [e]
