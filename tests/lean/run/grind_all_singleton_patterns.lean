module
example (p : Nat → Prop) (h₁ : x < n) (h₂ : ¬ p x) : ∃ i, i < n ∧ ¬ p i := by
  grind

example (p : Nat → Prop) (h : ¬ p x) : ∃ i, ¬ p i := by
  grind

example (p : Nat → Prop) (h₁ : x < n) (h₂ : ¬ p x) : ¬ (∀i < n, p i) := by
  grind

@[grind] def A (p q : Prop) := p ∧ q

example (p q : Nat → Prop) (h : ∀ x, A (p x) (q x)) : q a := by
  grind

example (p q r : Nat → Prop) (h : ∀ x, A (p x) (A (r x) (q x))) : r a := by
  grind
