module
import all Lean.PremiseSelection.SineQuaNon
import Lean.Meta.Basic
import Std.Data.ExtHashMap

open Lean PremiseSelection SineQuaNon

set_premise_selector Lean.PremiseSelection.sineQuaNonSelector

example {x : Dyadic} {prec : Int} : x.roundDown prec ≤ x := by
  fail_if_success grind
  grind +premises

example {x : Dyadic} {prec : Int} : (x.roundUp prec).precision ≤ some prec := by
  fail_if_success grind
  grind +premises

/-- info: [(HAppend.hAppend, 1.000000)] -/
#guard_msgs in
run_meta do
  let r ← triggerSymbols (← getConstInfo `List.append_assoc)
  logInfo m!"{r}"

/-- info: [(HAppend.hAppend, 1.000000)] -/
#guard_msgs in
run_meta do
  let r ← sineQuaNonTriggersFor `List.append_assoc
  logInfo m!"{r}"

/-- info: true -/
#guard_msgs in
run_meta do
  let r ← sineQuaNonTheorems `Std.ExtHashMap.erase
  logInfo m!"{r.contains (`Std.ExtHashMap.getElem_erase, 1.00)}"

/-- info: [Std.ExtHashMap.contains, Std.ExtHashMap.erase] -/
#guard_msgs in
run_meta do
  let r ← triggerSymbols (← getConstInfo `Std.ExtHashMap.contains_erase)
  logInfo m!"{r.map (·.1)}"

/-- info: [Std.ExtHashMap.contains, Std.ExtHashMap.erase] -/
#guard_msgs in
run_meta do
  let r ← sineQuaNonTriggersFor `Std.ExtHashMap.contains_erase
  logInfo m!"{r.map (·.1)}"
