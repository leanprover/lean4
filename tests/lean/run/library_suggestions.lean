import Lean.LibrarySuggestions

/--
error: Type mismatch
  Nat
has type
  Type
of sort `Type 1` but is expected to have type
  Lean.LibrarySuggestions.Selector
of sort `Type`
---
error: Failed to elaborate Nat as a `MVarId → Config → MetaM (Array Suggestion)`.
-/
#guard_msgs in
set_library_suggestions Nat

/--
error: No library suggestions engine registered. (Note that Lean does not provide a default library suggestions engine, these must be provided by a downstream library, and configured using `set_library_suggestions`.)
-/
#guard_msgs in
example : True := by
  suggestions
  trivial

set_library_suggestions (fun _ _ => pure #[])

/-- info: Library suggestions: [] -/
#guard_msgs in
example : True := by
  suggestions
  trivial

set_library_suggestions Lean.LibrarySuggestions.random ⟨1,1⟩

-- This would be an extremely fragile test (select 10 random constants!)
-- so we do not use #guard_msgs.
example : True := by
  suggestions
  trivial
