example (A : Type₁) (a₁ a₂ : A) : a₁ = a₂ →
 (λ (B : Type₁) (f : A → B), f a₁) = (λ (B : Type₁) (f : A → B), f a₂) :=
by simp
