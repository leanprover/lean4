import Lean.PremiseSelection

/--
error: type mismatch
  Nat
has type
  Type : Type 1
but is expected to have type
  Lean.PremiseSelection.Selector : Type
---
error: Failed to elaborate Nat as a `MVarId → Config → MetaM (Array Suggestion)`.
-/
#guard_msgs in
set_premise_selector Nat

/--
error: No premise selector registered. (Note the Lean does not provide a default premise selector, these must be installed by a downstream library.)
-/
#guard_msgs in
example : True := by
  suggest_premises
  trivial

set_premise_selector (fun _ _ => pure #[])

/-- info: Premise suggestions: [] -/
#guard_msgs in
example : True := by
  suggest_premises
  trivial

set_premise_selector Lean.PremiseSelection.random ⟨1,1⟩

-- This would be an extremely fragile test (select 10 random constants!)
-- so we do not use #guard_msgs.
example : True := by
  suggest_premises
  trivial
