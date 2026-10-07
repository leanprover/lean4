module

/-!
`#print axioms` in a `module` collects the axioms of imported declarations, whose proofs are not
loaded, from the private data of the imported modules.
-/

public theorem em' (p : Prop) : p ∨ ¬p := Classical.em p

/-- info: 'em'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms em'

/-- info: 'Classical.em' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Classical.em

/-- info: 'Nat.add_comm' does not depend on any axioms -/
#guard_msgs in
#print axioms Nat.add_comm

public axiom localAx : True

public theorem mixed (p : Prop) : (p ∨ ¬p) ∧ True := ⟨Classical.em p, localAx⟩

/-- info: 'mixed' depends on axioms: [localAx, propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mixed

/-! Declarations that only depend on the current module need no imported data. -/

public theorem onlyLocal : True := localAx

/-- info: 'onlyLocal' depends on axioms: [localAx] -/
#guard_msgs in
#print axioms onlyLocal

/-! `#eval` detects `sorry` in the current module. -/

/-- warning: declaration uses `sorry` -/
#guard_msgs in
public theorem localSorry : True := sorry

/--
error: Aborting evaluation since the expression depends on the 'sorry' axiom, which can lead to runtime instability and crashes.

To attempt to evaluate anyway despite the risks, use the '#eval!' command.
-/
#guard_msgs in
#eval (fun (_ : True) => (1 : Nat)) localSorry

/-- info: 1 -/
#guard_msgs in
#eval! (fun (_ : True) => (1 : Nat)) localSorry
