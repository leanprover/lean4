import Lean.LibrarySuggestions.Basic

/-!
# Test: Private theorems should appear in currentFile suggestions

Private theorems (declared with `private theorem`) have mangled names starting with
`_private.` which would normally be filtered by `isInternalDetail`. However, since
they're accessible from the current module, `currentFile` should include them.
-/

-- A public theorem for comparison
theorem publicTheorem : True := trivial

-- A private theorem that should still appear in currentFile suggestions
private theorem privateTheorem : 1 + 1 = 2 := rfl

-- Test the currentFile selector
set_library_suggestions Lean.LibrarySuggestions.currentFile

-- Both public and private theorems should appear.
-- The private theorem has a mangled name like `_private.library_suggestions_private.0.privateTheorem`
-- but should still be suggested since currentFile uses allowPrivate := true.
/--
info: Library suggestions:
  publicTheorem
  privateTheorem
-/
#guard_msgs in
example : True := by
  suggestions
  trivial
