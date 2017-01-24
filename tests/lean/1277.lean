variables {α₁ : Type} {α₂ : α₁ → Type} {β₁ : Type} {β₂ : β₁ → Type}

def map (f₁ : α₁ → β₁) (f₂ : Π⦃a⦄, α₂ a → β₂ (f₁ a)) : (Σa, α₂ a) → (Σb, β₂ b)
| ⟨a₁, a₂⟩ := ⟨f₁ a₁, f₂ a₂⟩

set_option trace.check true

example (f₁ : α₁ → α₁) (f₂ : Π⦃a⦄, α₂ a → α₂ (f₁ a)) (eq₁ : f₁ = id) : map f₁ f₂ = id :=
begin
  rw [eq₁],
end
