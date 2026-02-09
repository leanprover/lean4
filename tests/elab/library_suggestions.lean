import Lean.LibrarySuggestions

/--
error: Type mismatch
  Nat
has type
  Type
of sort `Type 1` but is expected to have type
  Lean.LibrarySuggestions.Selector
of sort `Type`
-/
#guard_msgs in
set_library_suggestions Nat

set_library_suggestions (fun _ _ => pure #[])

/-- info: Library suggestions: -/
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
