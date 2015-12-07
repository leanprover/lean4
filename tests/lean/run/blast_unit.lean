-- Testing all possible cases of [unit_action]
set_option blast.recursor false
variables {A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ : Prop}

-- H first, all pos
example (H : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄) (a1 : A₁) (a2 : A₂) (a3 : A₃) (n1 : ¬ B₁) (n2 : ¬ B₂) (n3 : ¬ B₃) : B₄ := by blast
example (H : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄) (a1 : A₁) (a2 : A₂) (a3 : A₃) (n1 : ¬ B₁) (n2 : ¬ B₂) (n3 : ¬ B₄) : B₃ := by blast
example (H : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄) (a1 : A₁) (a2 : A₂) (a3 : A₃) (n1 : ¬ B₁) (n3 : ¬ B₃) (n3 : ¬ B₄) : B₂ := by blast
example (H : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄) (a1 : A₁) (a2 : A₂) (a3 : A₃) (n2 : ¬ B₂) (n3 : ¬ B₃) (n3 : ¬ B₄) : B₁ := by blast

example (H : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄) (a1 : A₁) (a2 : A₂) (n1 : ¬ B₁) (n2 : ¬ B₂) (n3 : ¬ B₃) (n3 : ¬ B₄) : ¬ A₃ := by blast
example (H : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄) (a1 : A₁) (a3 : A₃) (n1 : ¬ B₁) (n2 : ¬ B₂) (n3 : ¬ B₃) (n3 : ¬ B₄) : ¬ A₂ := by blast
example (H : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄) (a2 : A₂) (a3 : A₃) (n1 : ¬ B₁) (n2 : ¬ B₂) (n3 : ¬ B₃) (n3 : ¬ B₄) : ¬ A₁ := by blast

-- H last, all pos
example (a1 : A₁) (a2 : A₂) (a3 : A₃) (n1 : ¬ B₁) (n2 : ¬ B₂) (n3 : ¬ B₃) (H : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄) : B₄ := by blast
example (a1 : A₁) (a2 : A₂) (a3 : A₃) (n1 : ¬ B₁) (n2 : ¬ B₂) (n3 : ¬ B₄) (H : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄) : B₃ := by blast
example (a1 : A₁) (a2 : A₂) (a3 : A₃) (n1 : ¬ B₁) (n3 : ¬ B₃) (n3 : ¬ B₄) (H : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄) : B₂ := by blast
example (a1 : A₁) (a2 : A₂) (a3 : A₃) (n2 : ¬ B₂) (n3 : ¬ B₃) (n3 : ¬ B₄) (H : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄) : B₁ := by blast

example (a1 : A₁) (a2 : A₂) (n1 : ¬ B₁) (n2 : ¬ B₂) (n3 : ¬ B₃) (n3 : ¬ B₄) (H : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄) : ¬ A₃ := by blast
example (a1 : A₁) (a3 : A₃) (n1 : ¬ B₁) (n2 : ¬ B₂) (n3 : ¬ B₃) (n3 : ¬ B₄) (H : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄) : ¬ A₂ := by blast
example (a2 : A₂) (a3 : A₃) (n1 : ¬ B₁) (n2 : ¬ B₂) (n3 : ¬ B₃) (n3 : ¬ B₄) (H : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄) : ¬ A₁ := by blast

-- H first, all neg
example (H : ¬ A₁ → ¬ A₂ → ¬ A₃ → ¬ B₁ ∨ ¬ B₂ ∨ ¬ B₃ ∨ ¬ B₄) (n1 : ¬ A₁) (n2 : ¬ A₂) (n3 : ¬ A₃) (b1 : B₁) (b2 : B₂) (b3 : B₃) : ¬ B₄ := by blast
example (H : ¬ A₁ → ¬ A₂ → ¬ A₃ → ¬ B₁ ∨ ¬ B₂ ∨ ¬ B₃ ∨ ¬ B₄) (n1 : ¬ A₁) (n2 : ¬ A₂) (n3 : ¬ A₃) (b1 : B₁) (b2 : B₂) (b4 : B₄) : ¬ B₃ := by blast
example (H : ¬ A₁ → ¬ A₂ → ¬ A₃ → ¬ B₁ ∨ ¬ B₂ ∨ ¬ B₃ ∨ ¬ B₄) (n1 : ¬ A₁) (n2 : ¬ A₂) (n3 : ¬ A₃) (b1 : B₁) (b3 : B₃) (b4 : B₄) : ¬ B₂ := by blast
example (H : ¬ A₁ → ¬ A₂ → ¬ A₃ → ¬ B₁ ∨ ¬ B₂ ∨ ¬ B₃ ∨ ¬ B₄) (n1 : ¬ A₁) (n2 : ¬ A₂) (n3 : ¬ A₃) (b2 : B₂) (b3 : B₃) (b4 : B₄) : ¬ B₁ := by blast

example (H : ¬ A₁ → ¬ A₂ → ¬ A₃ → ¬ B₁ ∨ ¬ B₂ ∨ ¬ B₃ ∨ ¬ B₄) (n1 : ¬ A₁) (n2 : ¬ A₂) (b1 : B₁) (b2 : B₂) (b3 : B₃) (b4 : B₄) : ¬ ¬ A₃ := by blast
example (H : ¬ A₁ → ¬ A₂ → ¬ A₃ → ¬ B₁ ∨ ¬ B₂ ∨ ¬ B₃ ∨ ¬ B₄) (n1 : ¬ A₁) (n3 : ¬ A₃) (b1 : B₁) (b2 : B₂) (b3 : B₃) (b4 : B₄) : ¬ ¬ A₂ := by blast
example (H : ¬ A₁ → ¬ A₂ → ¬ A₃ → ¬ B₁ ∨ ¬ B₂ ∨ ¬ B₃ ∨ ¬ B₄) (n2 : ¬ A₂) (n3 : ¬ A₃) (b1 : B₁) (b2 : B₂) (b3 : B₃) (b4 : B₄) : ¬ ¬ A₁ := by blast

-- H last, all neg
example (n1 : ¬ A₁) (n2 : ¬ A₂) (n3 : ¬ A₃) (b1 : B₁) (b2 : B₂) (b3 : B₃) (H : ¬ A₁ → ¬ A₂ → ¬ A₃ → ¬ B₁ ∨ ¬ B₂ ∨ ¬ B₃ ∨ ¬ B₄) : ¬ B₄ := by blast
example (n1 : ¬ A₁) (n2 : ¬ A₂) (n3 : ¬ A₃) (b1 : B₁) (b2 : B₂) (b4 : B₄) (H : ¬ A₁ → ¬ A₂ → ¬ A₃ → ¬ B₁ ∨ ¬ B₂ ∨ ¬ B₃ ∨ ¬ B₄) : ¬ B₃ := by blast
example (n1 : ¬ A₁) (n2 : ¬ A₂) (n3 : ¬ A₃) (b1 : B₁) (b3 : B₃) (b4 : B₄) (H : ¬ A₁ → ¬ A₂ → ¬ A₃ → ¬ B₁ ∨ ¬ B₂ ∨ ¬ B₃ ∨ ¬ B₄) : ¬ B₂ := by blast
example (n1 : ¬ A₁) (n2 : ¬ A₂) (n3 : ¬ A₃) (b2 : B₂) (b3 : B₃) (b4 : B₄) (H : ¬ A₁ → ¬ A₂ → ¬ A₃ → ¬ B₁ ∨ ¬ B₂ ∨ ¬ B₃ ∨ ¬ B₄) : ¬ B₁ := by blast

example (n1 : ¬ A₁) (n2 : ¬ A₂) (b1 : B₁) (b2 : B₂) (b3 : B₃) (b4 : B₄) (H : ¬ A₁ → ¬ A₂ → ¬ A₃ → ¬ B₁ ∨ ¬ B₂ ∨ ¬ B₃ ∨ ¬ B₄) : ¬ ¬ A₃ := by blast
example (n1 : ¬ A₁) (n3 : ¬ A₃) (b1 : B₁) (b2 : B₂) (b3 : B₃) (b4 : B₄) (H : ¬ A₁ → ¬ A₂ → ¬ A₃ → ¬ B₁ ∨ ¬ B₂ ∨ ¬ B₃ ∨ ¬ B₄) : ¬ ¬ A₂ := by blast
example (n2 : ¬ A₂) (n3 : ¬ A₃) (b1 : B₁) (b2 : B₂) (b3 : B₃) (b4 : B₄) (H : ¬ A₁ → ¬ A₂ → ¬ A₃ → ¬ B₁ ∨ ¬ B₂ ∨ ¬ B₃ ∨ ¬ B₄) : ¬ ¬ A₁ := by blast
