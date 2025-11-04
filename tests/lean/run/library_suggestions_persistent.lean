import Lean.LibrarySuggestions
import Lean.Meta.Basic
import Std.Data.ExtHashMap

/-!
# Test that library suggestions persist across file boundaries

This test verifies that the default library suggestion engine set in
`Lean.LibrarySuggestions.Default` is correctly persisted when imported via `Lean.LibrarySuggestions`.

We do NOT call `set_library_suggestions` in this file - the selector should
already be set from importing Lean.LibrarySuggestions (which imports Default).
-/

/--
info: ✓ Selector found in imported state: `Lean.LibrarySuggestions.sineQuaNonSelector
---
info:   ✓ Successfully retrieved selector using getSelector!
-/
#guard_msgs in
open Lean Lean.LibrarySuggestions in
run_cmd do
  let stx? := librarySuggestionsExt.getState (← getEnv)
  match stx? with
  | none => Lean.logInfo "❌ No selector found in imported state!"
  | some stx =>
    Lean.logInfo s!"✓ Selector found in imported state: {stx}"
    -- Try to retrieve the selector using getSelector
    Elab.Command.liftTermElabM do
      let selector? ← getSelector
      match selector? with
      | none => Lean.logInfo "  ❌ getSelector returned none"
      | some _ => Lean.logInfo "  ✓ Successfully retrieved selector using getSelector!"

-- These examples should work with grind +suggestions but not grind alone
-- (proving that the suggestions engine is active and helping)

example {x : Dyadic} {prec : Int} : x.roundDown prec ≤ x := by
  fail_if_success grind
  grind +suggestions

example {x : Dyadic} {prec : Int} : (x.roundUp prec).precision ≤ some prec := by
  fail_if_success grind
  grind +suggestions
