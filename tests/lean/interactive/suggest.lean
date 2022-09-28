import Lean.Meta.Tactic.Suggest

theorem asdf : (x : Nat) → x = x := by
  suggest
  intro
  rfl
