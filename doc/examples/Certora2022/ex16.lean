/- Inaccessible names -/

example : ∀ x y : Nat, x = y → y = x := by
  intros
  apply Eq.symm
  assumption

example : ∀ x y : Nat, x = y → y = x := by
  intros
  apply Eq.symm
  rename_i a b hab
  exact hab
