/-!
# Testing `intro` with `letFun`
-/

/-!
Explicit `intro`.
-/
example : have x := 2; ∀ _ : Nat, x = x := by
  intro x _
  rfl

/-!
`intros` is aware of `letFun`.
-/
example : have x := 2; ∀ _ : Nat, x = x := by
  intros
  rfl
