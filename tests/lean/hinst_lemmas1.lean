axiom foo1 : ∀ (a b c : nat), b > a → b < c  → a < c
axiom foo2 : ∀ (a b c : nat), b > a → b < c → a < c
axiom foo3 : ∀ (a b c : nat), b > a → b < c + c → a < c + c


run_cmd
do
  hs ← return $ hinst_lemmas.mk,
  h₁ ← hinst_lemma.mk_from_decl `foo1,
  h₂ ← hinst_lemma.mk_from_decl_core tactic.transparency.none `foo2 ff,
  h₃ ← hinst_lemma.mk_from_decl `foo3,
  hs ← return $ ((hs^.add h₁)^.add h₂)^.add h₃,
  hs^.pp >>= tactic.trace
