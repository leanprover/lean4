import Lean
set_option warn.sorry false

/-!
`Theorem.rewrite` must restore maximal sharing for discharger-provided proofs that occur
in the theorem's `rhs`: the proof becomes part of the resulting term, which must satisfy
the `SymM` sharing invariant (checked by `sym.debug`). Dischargers are not required to
return maximally shared proofs.
-/

open Lean Meta Sym Simp

axiom foo : True ∧ True → Prop
axiom P : Prop
axiom Q : Prop

/-- The discharged hypothesis `h` occurs in the `rhs`. -/
theorem thm1 (h : True ∧ True) : P = foo h := sorry

/-- The discharged hypothesis `h` does not occur in the `rhs`. -/
theorem thm2 (_h : True ∧ True) : P = Q := sorry

/-- Returns a proof that is not maximally shared. -/
def discharger : Discharger := fun _ =>
  return .solved <| mkApp4 (mkConst ``And.intro)
    (mkConst ``True) (mkConst ``True) (mkConst ``True.intro) (mkConst ``True.intro)

def test (declName : Name) : MetaM Unit := SymM.run do
  let thm ← mkTheoremFromDecl declName
  let e ← shareCommon (mkConst ``P)
  let r ← SimpM.run' (thm.rewrite e discharger)
  match r with
  | .step e' proof _ _ =>
    check proof
    logInfo m!"step: {e'}"
  | _ => throwError "expected the rewrite to fire"

/-- info: step: foo ⋯ -/
#guard_msgs in
set_option sym.debug true in
run_meta test ``thm1

/-- info: step: Q -/
#guard_msgs in
set_option sym.debug true in
run_meta test ``thm2
