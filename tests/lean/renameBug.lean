theorem ex : ∀ a b c : Nat, a = b → a = c → c = b := by
  intros
  rename _ = c => h1
  apply Eq.symm
  assumption
  assumption
