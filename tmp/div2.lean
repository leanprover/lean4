def R : (Σ _ : nat, nat) → (Σ _ : nat, nat) → Prop :=
sigma.lex nat.lt (λ _, empty_relation)

def Rwf : well_founded R :=
sigma.lex_wf nat.lt_wf (λ _, empty_wf)

set_option trace.debug.eqn_compiler.wf_rec true
set_option trace.eqn_compiler.wf_rec true
set_option trace.app_builder true
-- set_option trace.eqn_compiler.elim_match true

def Div : nat → Prop → nat → nat
| x p y :=
  if h : 0 < y ∧ y ≤ x
  then
    have x - y < x, from nat.sub_lt (nat.lt_of_lt_of_le h.left h.right) h.left,
    Div (x - y) p y + 1
  else 0
-- using_well_founded R Rwf
