-- Backward chaining with hypotheses
constants {P Q R S T U : Prop}
constants (Huq : U → Q) (Hur : U → R) (Hus : U → S) (Hut : U → T)
attribute [intro] Huq Hur Hus Hut

open tactic

definition lemma4 : (P → Q) → (Q → R) → (R → S) → (S → T) → P → T :=
by do
  H1 ← intro `H1,
  H2 ← intro `H2,
  H3 ← intro `H3,
  H4 ← intro `H4,
  H5 ← intro `H5,
  /- Construct lemma set manually -/
  lemmas ← mk_back_lemmas,
  trace "lemmas for target: ",
  target >>= back_lemmas_find lemmas >>= trace >> trace "-----",
  trace "lemmas for H3 body: ",
  infer_type H3 >>= (λ t, back_lemmas_find lemmas (expr.binding_body t)) >>= trace >> trace "-----",
  lemmas ← back_lemmas_insert lemmas H1,
  lemmas ← back_lemmas_insert lemmas H2,
  lemmas ← back_lemmas_insert lemmas H3,
  lemmas ← back_lemmas_insert lemmas H4,
  lemmas ← back_lemmas_insert lemmas H5,
  trace "lemmas for H3 body (after update): ",
  infer_type H3 >>= (λ t, back_lemmas_find lemmas (expr.binding_body t)) >>= trace >> trace "-----",
  /- Execute backward_chaining_core using hand-crafted lemma set -/
  backward_chaining_core reducible tt 10 skip failed lemmas
