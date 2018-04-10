namespace test
universes u v

def equinumerous (α : Type u) (β : Type v) :=
∃ f : α → β, function.bijective f

local infix ` ≈ ` := equinumerous

@[refl] lemma refl {α} : α ≈ α := sorry
@[trans] lemma trans {α β γ} :
    α ≈ β → β ≈ γ → α ≈ γ := sorry

@[congr] lemma equinumerous.congr_eqn {α α' β β'} :
    α ≈ α' → β ≈ β' → (α ≈ β) = (α' ≈ β') := sorry

@[congr] lemma congr_sum {α α' β β'} :
    α ≈ α' → β ≈ β' → (α ⊕ β) ≈ (α' ⊕ β') := sorry

@[simp] lemma eqn_ulift {α} : ulift α ≈ α := sorry

@[simp] lemma sum_empty {α} : (α ⊕ empty) ≈ α := sorry

-- rewriting `ulift empty` ==> `empty` changes the universe level
example {α : Type u} : (α ⊕ ulift empty) ≈ α := by simp
end test
