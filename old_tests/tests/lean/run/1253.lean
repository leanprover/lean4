open list
lemma induction₂ {α₁ α₂ : Type*} (p : list α₁ → list α₂ → Prop)
                 (h_base : p [] [])
                 (h_step : ∀ {xs₁ xs₂}, p xs₁ xs₂ → (∀ x₁ x₂, p (x₁::xs₁) (x₂::xs₂))) :
      Π (xs₁ : list α₁) (xs₂ : list α₂) (H_same_len : length xs₁ = length xs₂), p xs₁ xs₂

| []        []        h := h_base
| (x₁::xs₁) (x₂::xs₂) h := h_step (induction₂ xs₁ xs₂ sorry) x₁ x₂
