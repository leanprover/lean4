/- intro tactic variants -/

example (p q : α → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro h
  match h with
  | Exists.intro w (And.intro hp hq) => exact Exists.intro w (And.intro hq hp)

example (p q : α → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro (Exists.intro _ (And.intro hp hq))
  exact Exists.intro _ (And.intro hq hp)

example (p q : α → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro ⟨_, hp, hq⟩
  exact ⟨_, hq, hp⟩

example (α : Type) (p q : α → Prop) : (∃ x, p x ∨ q x) → ∃ x, q x ∨ p x := by
  intro
    | ⟨_, .inl h⟩ => exact ⟨_, .inr h⟩
    | ⟨_, .inr h⟩ => exact ⟨_, .inl h⟩
