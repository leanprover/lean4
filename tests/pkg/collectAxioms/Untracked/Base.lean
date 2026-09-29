module

/-! Declarations compiled with `trackAxioms := false` (see `lakefile.lean`). -/

public axiom untrackedAx : True

public theorem untrackedThm : True := untrackedAx

public theorem untrackedClean : True := trivial

/-! Axiom tracking is disabled in the current module. -/

/--
error: cannot collect the axioms of 'untrackedClean': axiom tracking is disabled in the current module (`trackAxioms := false`); use `lake check` to check the axioms used by the project instead
-/
#guard_msgs in
#print axioms untrackedClean
