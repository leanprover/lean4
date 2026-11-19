-- It's critical that this test remains a `module`:
-- its purpose is to test the availability of the selector in modules.
module
import Lean

/-!
# Test that library suggestions persist across file boundaries

This test verifies that the default library suggestion engine set in
`Lean.LibrarySuggestions.Default` is correctly persisted when imported via `Lean.LibrarySuggestions`.

We do NOT call `set_library_suggestions` in this file - the selector should
already be set from importing Lean.LibrarySuggestions (which imports Default).
-/

/--
info: ✓ Selector registered in imported state
---
info:   ✓ getSelector succeeded
-/
#guard_msgs in
open Lean Lean.LibrarySuggestions in
run_cmd do
  -- Check if a selector is registered
  let hasSelector := (librarySuggestionsExt.getState (← getEnv)).isSome
  if hasSelector then
    Lean.logInfo "✓ Selector registered in imported state"
    -- Try to retrieve the selector using getSelector
    Elab.Command.liftTermElabM do
      let selector? ← getSelector
      match selector? with
      | none => Lean.logInfo "  ❌ getSelector returned none"
      | some _ => Lean.logInfo "  ✓ getSelector succeeded"
  else
    Lean.logInfo "❌ No selector registered in imported state!"
