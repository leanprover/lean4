module

public import CollectAxioms.Left
public import CollectAxioms.Right
public import CollectAxioms.Chain.Top
public import CollectAxioms.Chain.Middle
public import CollectAxioms.Chain.Bottom
public import CollectAxioms.Inductive

/-! ## Diamond imports with same-named private axioms

Both Left and Right define `private axiom ax` and use it in the proof of a public theorem.
The private axioms get distinct mangled names. -/

public theorem combined : True ∧ True := ⟨leftThm, rightThm⟩

/-- info: 'combined' depends on axioms: [_private.CollectAxioms.Left.0.ax, _private.CollectAxioms.Right.0.ax] -/
#guard_msgs in
#print axioms combined

/-- info: 'leftThm' depends on axioms: [_private.CollectAxioms.Left.0.ax] -/
#guard_msgs in
#print axioms leftThm

/-- info: 'rightThm' depends on axioms: [_private.CollectAxioms.Right.0.ax] -/
#guard_msgs in
#print axioms rightThm

/-! ## Import chain with stripped def

Bottom defines a public axiom, Middle defines a public def (body stripped on export)
that uses it, Top defines a public theorem using that def. The axiom dependency
propagates through the stripped def. -/

/-- info: 'chainThm' depends on axioms: [chainAx] -/
#guard_msgs in
#print axioms chainThm

/-- info: 'chainDef' depends on axioms: [chainAx] -/
#guard_msgs in
#print axioms chainDef

/-! ## Axiom-free definitions -/

public def pureDef : Nat := 42

/-- info: 'pureDef' does not depend on any axioms -/
#guard_msgs in
#print axioms pureDef

/-! ## Opaque declaration -/

public opaque opaqueVal : Nat := 42

/-- info: 'opaqueVal' does not depend on any axioms -/
#guard_msgs in
#print axioms opaqueVal

/-! ## Axiom whose type mentions another axiom -/

public axiom myAxiom : Nat

public axiom axOfAx : myAxiom = myAxiom

/-- info: 'axOfAx' depends on axioms: [axOfAx, myAxiom] -/
#guard_msgs in
#print axioms axOfAx

/-! ## Multiple axiom dependencies -/

public noncomputable def usesMultiple : Nat := chainDef.casesOn myAxiom

/-- info: 'usesMultiple' depends on axioms: [chainAx, myAxiom] -/
#guard_msgs in
#print axioms usesMultiple

/-! ## Imported inductive blocks (#15226)

These queries must agree with the defining module, including for declarations whose
only dependency on the axiom is through the inductive type. -/

/-- info: 'S9' depends on axioms: [Classical.choice] -/
#guard_msgs in
#print axioms S9

/-- info: 'S9.mk' depends on axioms: [Classical.choice] -/
#guard_msgs in
#print axioms S9.mk

/-- info: 'usesS9' depends on axioms: [Classical.choice] -/
#guard_msgs in
#print axioms usesS9

/-- info: 'M1' depends on axioms: [Classical.choice] -/
#guard_msgs in
#print axioms M1

/-- info: 'M1.mk' depends on axioms: [Classical.choice] -/
#guard_msgs in
#print axioms M1.mk

/-- info: 'M2' depends on axioms: [Classical.choice] -/
#guard_msgs in
#print axioms M2

/-- info: 'M2.mk' depends on axioms: [Classical.choice] -/
#guard_msgs in
#print axioms M2.mk

/-- info: 'Nested' depends on axioms: [Classical.choice] -/
#guard_msgs in
#print axioms Nested

/-- info: 'Nested.mk' depends on axioms: [Classical.choice] -/
#guard_msgs in
#print axioms Nested.mk
