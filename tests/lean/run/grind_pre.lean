import Lean

open Lean Meta Elab Tactic Grind in
elab "grind_pre" : tactic => do
  liftMetaTactic fun mvarId => do
    let result ← Meta.Grind.Preprocessor.main mvarId
    return result.goals.map (·.mvarId) |>.toList

/--
warning: declaration uses 'sorry'
---
info: a b c : Bool
h : a = true ∧ (b = true ∨ c = true)
⊢ (b && a) = true
-/
#guard_msgs in
example (h : (a && (b || c)) = true) : b && a := by
  grind_pre
  trace_state
  sorry
