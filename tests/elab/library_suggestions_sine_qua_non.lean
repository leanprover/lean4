module
public import Lean.LibrarySuggestions.Basic
public import Lean.LibrarySuggestions.SineQuaNon
import all Lean.LibrarySuggestions.SineQuaNon
import Lean.Meta.Basic
import Std.Data.ExtHashMap

open Lean LibrarySuggestions SineQuaNon

set_library_suggestions Lean.LibrarySuggestions.sineQuaNonSelector

example {x : Dyadic} {prec : Int} : x.roundDown prec ≤ x := by
  fail_if_success grind
  grind +suggestions

example {x : Dyadic} {prec : Int} : (x.roundUp prec).precision ≤ some prec := by
  fail_if_success grind
  grind +suggestions

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
