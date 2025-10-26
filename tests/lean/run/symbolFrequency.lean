import Lean.Meta.Basic
import Lean.PremiseSelection.SymbolFrequency

open Lean PremiseSelection

/-- info: true -/
#guard_msgs in
run_meta do
  let f ← symbolFrequency `Nat
  logInfo m!"{decide (10000 < f)}"
