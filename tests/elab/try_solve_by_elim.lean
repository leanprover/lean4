/-
Tests for try? integration with solve_by_elim.

This tests that `try?` now includes `solve_by_elim` in its pipeline,
which is a prerequisite for removing the "first pass" solve_by_elim from `apply?`.
-/

set_option autoImplicit true

-- Basic hypothesis chaining: solve_by_elim can chain f and g to get from a to γ
-- This requires more than just `assumption` - it needs to apply f then g
example {α β γ : Type} (f : α → β) (g : β → γ) (a : α) : γ := by
  try?

-- Multi-step application: needs to apply f four times
example {α : Nat → Type} (f : (n : Nat) → α n → α (n+1)) (a : α 0) : α 4 := by
  try?

-- Backtracking case: needs to find the right combination of hypotheses
example (P₁ P₂ : α → Prop) (f : ∀ (a: α), P₁ a → P₂ a → β)
    (a : α) (_ha₁ : P₁ a)
    (a' : α) (ha'₁ : P₁ a') (ha'₂ : P₂ a') : β := by
  try?

-- Simple case that could be solved by either assumption or solve_by_elim
example (h : Nat) : Nat := by
  try?

-- Two-argument function application
example {α β : Type} (f : α → α → β) (a : α) : β := by
  try?
