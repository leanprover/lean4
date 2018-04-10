variables A : Type

example (s₁ s₂ s₃ : set A) : s₁ ⊆ s₂ → s₂ ⊆ s₃ → s₁ ⊆ s₃ :=
assume h₁ h₂ a ains₁,
h₂ (h₁ ains₁)
