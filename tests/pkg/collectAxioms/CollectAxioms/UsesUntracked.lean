module

public import Untracked.Base

/-! A tracked module depending on a module compiled with `trackAxioms := false`. -/

public theorem viaUntracked : True := untrackedThm

public theorem notViaUntracked : True := trivial

/--
error: cannot collect the axioms of 'viaUntracked': it depends on declarations from `Untracked.Base`, compiled with `trackAxioms := false`; use `lake check` to check the axioms used by the project instead
-/
#guard_msgs in
#print axioms viaUntracked

/--
error: cannot collect the axioms of 'untrackedClean': it depends on declarations from `Untracked.Base`, compiled with `trackAxioms := false`; use `lake check` to check the axioms used by the project instead
-/
#guard_msgs in
#print axioms untrackedClean

/-- info: 'notViaUntracked' does not depend on any axioms -/
#guard_msgs in
#print axioms notViaUntracked

/-! `#eval` checks the axioms it can see for `sorryAx` and does not fail on missing axiom data. -/

/-- info: 1 -/
#guard_msgs in
#eval (fun (_ : True) => (1 : Nat)) untrackedThm
