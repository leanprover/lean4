import Lean.LibrarySuggestions.Basic

-- Define a normal theorem that should appear in suggestions
theorem normalTheorem : True := trivial

-- Define a deprecated theorem that should be filtered out by isDeniedPremise
@[deprecated "Use normalTheorem instead" (since := "1970-01-01")]
theorem deprecatedTheorem : True := trivial

-- Another normal theorem to verify filtering is selective
theorem anotherNormalTheorem : 1 + 1 = 2 := rfl

-- Test the currentFile selector which uses isDeniedPremise to filter
set_library_suggestions Lean.LibrarySuggestions.currentFile

-- This test verifies that deprecated theorems are filtered out by isDeniedPremise
-- Expected: deprecatedTheorem should NOT appear in suggestions
/--
info: Library suggestions:
  normalTheorem
  anotherNormalTheorem
-/
#guard_msgs in
example : True := by
  suggestions
  trivial
