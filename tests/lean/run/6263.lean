import Lean

open Lean.Elab.Tactic

variable (p q : Prop)
theorem foo (h : p ∧ q) : q ∧ p := by
  run_tac liftMetaTactic1 (·.revertAll)
  guard_target =ₛ ∀ (p q : Prop), p ∧ q → q ∧ p
  sorry

theorem bla (h : p ∧ q) : q ∧ p := by
  revert p q
  guard_target =ₛ ∀ (p q : Prop), p ∧ q → q ∧ p
  sorry
