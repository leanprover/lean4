run_command
do
  tactic.trace "hinst_lemmas example:",
  hs ← return $ hinst_lemmas.mk,
  h₁ ← hinst_lemma.mk_from_decl `add_zero,
  h₂ ← hinst_lemma.mk_from_decl `zero_add,
  h₃ ← hinst_lemma.mk_from_decl `add_comm,
  hs ← return $ ((hs^.add h₁)^.add h₂)^.add h₃,
  hs^.pp >>= tactic.trace
