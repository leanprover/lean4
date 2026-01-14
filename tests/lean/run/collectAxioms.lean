import Lean

axiom A0 : Type
axiom A1 : Type

class C where
  a0 : A0

axiom A2 (_ : A1) : C

/--
info: #[`A2, `A1, `A0]
-/
#guard_msgs in
#eval Lean.collectAxioms ``A2

/--
info: 'A2' depends on axioms: [A0, A1, A2]
-/
#guard_msgs in
#print axioms A2

theorem one_add_one : 1 + 1 = 2 := by
  native_decide

/--
info: #[`Lean.ofReduceBool, `Lean.trustCompiler]
-/
#guard_msgs in
#eval Lean.collectAxioms ``one_add_one

/--
info: 'one_add_one' depends on axioms: [Lean.ofReduceBool, Lean.trustCompiler]
-/
#guard_msgs in
#print axioms one_add_one
