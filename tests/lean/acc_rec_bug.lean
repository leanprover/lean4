namespace play
inductive acc {A : Type} (R : A → A → Prop) : A → Prop :=
intro : ∀x, (∀ y, R y x → acc R y) → acc R x

variables {A : Type} (R : A → A → Prop) (C : A → Type) (x₁ : A) (ac : ∀y, R y x₁ → acc R y)
variable F : Πx, (Πy, R y x → C y) → C x

eval @acc.rec A R C (λ (x₂ : A)
                (ac : ∀y, R y x₂ → acc R y)
                (iH : Πy, R y x₂ → C y),
                   F x₂ iH)  x₁ (acc.intro x₁ ac)

check @acc.rec A R C (λ (x₂ : A)
                (ac : ∀y, R y x₂ → acc R y)
                (iH : Πy, R y x₂ → C y),
                   F x₂ iH)  x₁ (acc.intro x₁ ac)

check F x₁
  (λ (y : A) (a : R y x₁),
     acc.rec (λ (x₂ : A) (ac : ∀ (y : A), R y x₂ → acc R y) (iH : Π (y : A), R y x₂ → C y), F x₂ iH)
       (ac y a))
end play
