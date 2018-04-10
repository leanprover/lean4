example (A : Type) (B : A → Type) (b : B) : true :=
trivial

example : ∀ (A : Type) (B : A → Type) (b : B), true :=
begin
  intros, trivial
end

#check λ (A : Type) (B : A → Type) (b : B), true

#check λ (A : Type) (B : A → Type), B → true

#check λ (A : Type) (B : A → Type) b, (b : B)

example {A : Type} {B : Type} {a₁ a₂ : B} {b₁ b₂ : A → B} : a₁ = a₂ → (∀ x, b₁ x = b₂ x) → (let x : A := a₁ in b₁ x) = (let x : A := a₂ in b₂ x) :=
sorry
