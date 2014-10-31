import logic algebra.category.basic
open eq eq.ops category functor natural_transformation

variables {obC obD : Type} {C : category obC} {D : category obD} {F G H : C ⇒ D}

protected definition compose2 (η : G ⟹ H) (θ : F ⟹ G) : F ⟹ H :=
natural_transformation.mk
  (λ a, η a ∘ θ a)
  (λ a b f, calc
    H f ∘ (η a ∘ θ a) = (H f ∘ η a) ∘ θ a : assoc
                  ... = (η b ∘ G f) ∘ θ a : {naturality η f}
                  ... = η b ∘ (G f ∘ θ a) : assoc
                  ... = η b ∘ (θ b ∘ F f) : {naturality θ f}
                  ... = (η b ∘ θ b) ∘ F f : assoc)

theorem tst (a b c : num) (H₁ : ∀ x, b = x) (H₂ : c = b) : a = c :=
calc a  = b : H₁
    ... = c : H₂
