import Lean

-- Prints the equivalence class containing a `f` application
open Lean Meta Elab Tactic Grind in
elab "grind_test" : tactic => withMainContext do
  let declName := (← Term.getDeclName?).getD `_main
  Meta.Grind.preprocessAndProbe (← getMainGoal) declName do
    let trueExprs := (← filterENodes fun e => return e.self.isFVar && (← isEqTrue e.self)).toList.map (·.self)
    let falseExprs := (← filterENodes fun e => return e.self.isFVar && (← isEqFalse e.self)).toList.map (·.self)
    logInfo m!"true:  {trueExprs}"
    logInfo m!"false: {falseExprs}"

set_option grind.debug true

/--
info: true:  [q, w]
---
info: false: [p, r]
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : (p ∨ (q ∧ ¬r ∧ w)) → ¬p → False := by
  grind_test
  sorry

/--
info: true:  [r]
---
info: false: [p, q]
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : (p ∨ q ∨ r) → (p ∨ ¬q) → ¬p → False := by
  grind_test
  sorry

/--
info: true:  [r]
---
info: false: [p₁, q]
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : ((p₁ ∧ p₂) ∨ q ∨ r) → (p₁ ∨ ¬q) → p₁ = False → False := by
  grind_test
  sorry

/--
info: true:  [r]
---
info: false: [p₂, q]
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : ((p₁ ∧ p₂) ∨ q ∨ r) → ((p₂ ∧ p₁) ∨ ¬q) → p₂ = False → False := by
  grind_test
  sorry
