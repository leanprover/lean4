import Lean.Meta.Basic
import Lean.LibrarySuggestions.SymbolFrequency

open Lean LibrarySuggestions

/-- info: true -/
#guard_msgs in
run_meta do
  let f ← symbolFrequency `Nat
  logInfo m!"{decide (5000 < f)}"
