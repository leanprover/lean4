import data.set
open tactic

section
  universe variable u
  variables {α : Type u}

  example (a b c d₁ d₂ e₁ e₂ : set α) (f : set α → set α → set α) : b ∪ a = d₁ ∪ d₂ → b ∪ c = e₂ ∪ e₁ → f (a ∪ b ∪ c) (a ∪ b ∪ c) = f (c ∪ d₂ ∪ d₁) (e₂ ∪ a ∪ e₁) :=
  by cc
end
