import data.matrix data.real data.fin
open matrix real

axiom mx_add_comm {m n} (M₁ M₂ : matrix ℝ m n) : M₁ + M₂ = M₂ + M₁
attribute mx_add_comm [simp]
example (m n : ℕ) (M₁ M₂ : matrix ℝ m n) : M₁ + M₂ = M₂ + M₁ := by simp
