class Weight (ω : Type v) extends Add ω, Zero ω, LE ω, BEq ω, LawfulBEq ω where
  [decLe : DecidableLE ω]
  ε : ω

class Offset (α : Type u) (ω : Type v) [Weight ω] extends LE α, LT α, Std.IsPreorder α, Std.LawfulOrderLT α where
  offset      : α → ω → α
  offset_zero : ∀ a : α, offset a 0 = a
  offset_add  : ∀ (a : α) (k₁ k₂ : ω), offset (offset a k₁) k₂ = offset a (k₁ + k₂)
  offset_le   : ∀ (a b : α) (k : ω), offset a k ≤ offset b k ↔ a ≤ b
  weight_le   : ∀ (a : α) (k₁ k₂ : ω), offset a k₁ ≤ offset a k₂ → k₁ ≤ k₂
  weight_lt   : ∀ (a : α) (k₁ k₂ : ω), offset a k₁ < offset a k₂ → k₁ + ε ≤ k₂

namespace Offset

/-!
Just one transitivity theorem
-/
theorem le_offset_trans {α ω} [Weight ω] [Offset α ω]
    (a b c : α) (k₁ k₂ k₃ k₄ k : ω) :
    offset a k₁ ≤ offset b k₂ → offset b k₃ ≤ offset c k₄ → offset a (k₁ + k₃) ≤ offset c (k₂ + k₄) := by
  intro h₁ h₂
  rw [← offset_add]
  refine Std.le_trans ?_ ?_

theorem le_offset_trans₂ {α ω} [Weight ω] [Offset α ω]
    (a b c : α) (k₁ k₂ k₃ k₄ k : ω) :
    k₂ == k₃ + k → offset a k₁ ≤ offset b k₂ → offset b k₃ ≤ offset c k₄ → offset a k₁ ≤ offset c (k₄ + k) := by
  intro h h₁ h₂; simp at h; subst k₂
  replace h₂ := add_le_add' k h₂
  exact Std.le_trans h₁ h₂
