import Lean
open Lean Meta Elab Term Command

/-!
The `Int` linear normalizer of `simp +arith` must report no change on a term that is already in
normal form. It used to reify the literal `-1` as `.neg (.num 1)` while rendering the normalized
constant as `.num (-1)`, and so returned a proof of `e = e` for `d + k + -1`. Such a proof made
`simp` loop on a dependent forall over a `Prop` domain containing the term.
-/

/-- Runs `simp +arith` on the body of the given lambda and reports whether the term changed and whether a proof was produced. -/
elab "#check_arith " t:term : command => liftTermElabM do
  let e ← elabTerm t none
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  lambdaTelescope e fun _ body => do
    let ctx ← Simp.mkContext (config := { arith := true }) (simpTheorems := #[]) (congrTheorems := (← getSimpCongrTheorems))
    let (r, _) ← Simp.main body ctx (methods := ← Simp.mkDefaultMethods)
    logInfo m!"{body} ==> {r.expr}, same: {body == r.expr}, proof: {r.proof?.isSome}"

/-- info: r (d + k + -1) ==> r (d + k + -1), same: true, proof: false -/
#guard_msgs in
#check_arith fun (d k : Int) (r : Int → Prop) => r (d + k + -1)

/-- info: r (d + -1 * k) ==> r (d + -1 * k), same: true, proof: false -/
#guard_msgs in
#check_arith fun (d k : Int) (r : Int → Prop) => r (d + -1 * k)

/-- info: r (d + k + Int.neg 1) ==> r (d + k + -1), same: false, proof: true -/
#guard_msgs in
#check_arith fun (d k : Int) (r : Int → Prop) => r (d + k + Int.neg 1)

/-- info: r (d - k) ==> r (d + -1 * k), same: false, proof: true -/
#guard_msgs in
#check_arith fun (d k : Int) (r : Int → Prop) => r (d - k)

/-- info: r (-2 + k) ==> r (k + -2), same: false, proof: true -/
#guard_msgs in
#check_arith fun (k : Int) (r : Int → Prop) => r (-2 + k)

set_option maxRecDepth 512 in
example (d : Int) (k : Nat) (r : Int → Prop) (P : ∀ x : Int, r x → Prop)
    (h : ∀ (b : r (d + ↑k + -1)), P (d + ↑k + -1) b) :
    ∀ (b : r (↑k + d - 1)), P (↑k + d - 1) b := by
  simpa +arith only using h

-- Both `grind` normalizers keep `-1 = j`, like `j = -1`: an equation between a numeral and an
-- atom. Sym reifies `-1` the same way.
set_option warn.sorry false
example (j : Int) : -1 = j := by grind_norm; guard_target =ₛ -1 = j; sorry
example (j : Int) : -1 = j := by grind_norm sym; guard_target =ₛ -1 = j; sorry
#guard_msgs in
example (j : Int) : (2 : Int) * 3 - 7 = j := by grind_norm check; sorry
