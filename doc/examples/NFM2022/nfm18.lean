/- Structuring proofs (cont.) -/

example : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro h
  have hp : p := h.left
  have hqr : q ∨ r := h.right
  show (p ∧ q) ∨ (p ∧ r)
  cases hqr with
  | inl hq => exact Or.inl ⟨hp, hq⟩
  | inr hr => exact Or.inr ⟨hp, hr⟩

example : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro ⟨hp, hqr⟩
  cases hqr with
  | inl hq =>
    have := And.intro hp hq
    apply Or.inl; exact this
  | inr hr =>
    have := And.intro hp hr
    apply Or.inr; exact this
