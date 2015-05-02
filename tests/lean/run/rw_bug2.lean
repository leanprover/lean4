import logic.eq
open prod

definition swap {A : Type} : A × A → A × A
| (a, b) := (b, a)

theorem swap_swap {A : Type} : ∀ p : A × A, swap (swap p) = p
| (a, b) := rfl

theorem eq_of_swap_eq {A : Type} : ∀ p₁ p₂ : A × A, swap p₁ = swap p₂ → p₁ = p₂ :=
take p₁ p₂, assume seqs,
assert h₁ : swap (swap p₁) = swap (swap p₂), from congr_arg swap seqs,
by rewrite *swap_swap at h₁; exact h₁
