import Lean.LibrarySuggestions.Basic

-- Define some initial local constants
def myLocalDef : Nat := 42

theorem myLocalTheorem : myLocalDef = 42 := rfl

-- Add a theorem in the Lean namespace (should be filtered by isDeniedPremise)
namespace Lean
theorem shouldBeFiltered : True := trivial
end Lean

-- Test the currentFile selector (should only show theorems, not definitions)
set_library_suggestions Lean.LibrarySuggestions.currentFile

-- First test: should show only myLocalTheorem
-- (not myLocalDef since it's a def, not Lean.shouldBeFiltered since it's in Lean namespace)
/--
info: Library suggestions:
  myLocalTheorem
-/
#guard_msgs in
example : True := by
  suggestions
  trivial

-- Add more local constants (mix of theorems and definitions)
theorem anotherTheorem : True := trivial

def myFunction (x : Nat) : Nat := x + 1

-- Second test: should show only the two theorems (not myFunction)
/--
info: Library suggestions:
  myLocalTheorem
  anotherTheorem
-/
#guard_msgs in
example : False → True := by
  suggestions
  intro h
  trivial
