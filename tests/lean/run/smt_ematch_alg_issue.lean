lemma {u} ring_add_comm {α : Type u} [ring α] : ∀ (a b : α), (: a + b :) = b + a :=
add_comm

open smt_tactic
meta def no_ac : smt_config :=
{ default_smt_config with cc_cfg := { default_cc_config with ac := ff }}

example {α : Type} [field α] (a b : α) : a + b = b + a :=
begin [smt] with no_ac,
  ematch_using [ring_add_comm]
end
