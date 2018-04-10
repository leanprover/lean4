protected def rel : ℤ × ℤ → ℤ × ℤ → Prop
| ⟨n₁, d₁⟩ ⟨n₂, d₂⟩ := n₁ * d₂ = n₂ * d₁

private def mul' : ℤ × ℤ → ℤ × ℤ → ℤ × ℤ
| ⟨n₁, d₁⟩ ⟨n₂, d₂⟩ := ⟨n₁ * n₂, d₁ * d₂⟩

example : ∀(a b c d : ℤ × ℤ), rel a c → rel b d → rel (mul' a b) (mul' c d) :=
λ⟨n₁, d₁⟩ ⟨n₂, d₂⟩ ⟨n₃, d₃⟩ ⟨n₄, d₄⟩,
  assume (h₁ : n₁ * d₃ = n₃ * d₁) (h₂ : n₂ * d₄ = n₄ * d₂),
  show (n₁ * n₂) * (d₃ * d₄) = (n₃ * n₄) * (d₁ * d₂),
    by cc
