def α : Type := ℕ → ℕ

set_option trace.app_builder true
example (x y : α) (H : x = y) (n : ℕ) : x n = y n :=
by simp [H]

example (x y : α) (H₁ : x = y) (m n : ℕ) (H₂ : m = n) : x m = y n :=
by simp [H₁, H₂]
