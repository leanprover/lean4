module

import all Lean.LibrarySuggestions.SymbolFrequency
import all Init.Data.Array.Basic

open Lean LibrarySuggestions

/-- info: [List, Eq, HAppend.hAppend] -/
#guard_msgs in
run_meta do
  let ci ← getConstInfo `List.append_assoc
  let consts ← ci.type.foldRelevantConstants (init := #[]) (fun n ns => return ns.push n)
  logInfo m!"{consts}"

/-- info: [List, Ne, HAppend.hAppend, List.nil, Eq, List.head] -/
#guard_msgs in
run_meta do
  let ci ← getConstInfo `List.head_append_right
  let consts ← ci.type.foldRelevantConstants (init := #[]) (fun n ns => return ns.push n)
  logInfo m!"{consts}"

/-- info: [Array, Nat, LT.lt, Array.size, HAdd.hAdd, OfNat.ofNat, Array.swap, Not] -/
#guard_msgs in
run_meta do
  let ci ← getConstInfo `Array.eraseIdx.induct
  let consts ← ci.type.foldRelevantConstants (init := #[]) (fun n ns => return ns.push n)
  logInfo m!"{consts}"
