/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Grind.Lemmas
import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.Tactic.Grind.Internalize
import Lean.Meta.Tactic.Grind.Simp
import Lean.Meta.Tactic.Grind.EqResolution

namespace Lean.Meta.Grind
/--
If `parent` is a projection-application `proj_i c`,
check whether the root of the equivalence class containing `c` is a constructor-application `ctor ... a_i ...`.
If so, internalize the term `proj_i (ctor ... a_i ...)` and add the equality `proj_i (ctor ... a_i ...) = a_i`.
-/
def propagateForallPropUp (e : Expr) : GoalM Unit := do
  let .forallE n p q bi := e | return ()
  trace_goal[grind.debug.forallPropagator] "{e}"
  if !q.hasLooseBVars then
    propagateImpliesUp p q
  else
    unless (← isEqTrue p) do return
    trace_goal[grind.debug.forallPropagator] "isEqTrue, {e}"
    let h₁ ← mkEqTrueProof p
    let qh₁ := q.instantiate1 (mkOfEqTrueCore p h₁)
    let r ← simp qh₁
    let q := mkLambda n bi p q
    let q' := r.expr
    internalize q' (← getGeneration e)
    trace_goal[grind.debug.forallPropagator] "q': {q'} for{indentExpr e}"
    let h₂ ← r.getProof
    let h := mkApp5 (mkConst ``Lean.Grind.forall_propagator) p q q' h₁ h₂
    pushEq e q' h
where
  propagateImpliesUp (a b : Expr) : GoalM Unit := do
    unless (← alreadyInternalized b) do return ()
    if (← isEqFalse a) then
      -- a = False → (a → b) = True
      pushEqTrue e <| mkApp3 (mkConst ``Grind.imp_eq_of_eq_false_left) a b (← mkEqFalseProof a)
    else if (← isEqTrue a) then
      -- a = True → (a → b) = b
      pushEq e b <| mkApp3 (mkConst ``Grind.imp_eq_of_eq_true_left) a b (← mkEqTrueProof a)
    else if (← isEqTrue b) then
      -- b = True → (a → b) = True
      pushEqTrue e <| mkApp3 (mkConst ``Grind.imp_eq_of_eq_true_right) a b (← mkEqTrueProof b)

private def isEqTrueHyp? (proof : Expr) : Option FVarId := Id.run do
  let_expr eq_true _ p := proof | return none
  let .fvar fvarId := p | return none
  return some fvarId

/-- Similar to `mkEMatchTheoremWithKind?`, but swallow any exceptions. -/
private def mkEMatchTheoremWithKind'? (origin : Origin) (proof : Expr) (kind : TheoremKind) : MetaM (Option EMatchTheorem) := do
  try
    mkEMatchTheoremWithKind? origin #[] proof kind
  catch _ =>
    return none

private def addLocalEMatchTheorems (e : Expr) : GoalM Unit := do
  let proof ← mkEqTrueProof e
  let origin ← if let some fvarId := isEqTrueHyp? proof then
    pure <| .fvar fvarId
  else
    let idx ← modifyGet fun s => (s.nextThmIdx, { s with nextThmIdx := s.nextThmIdx + 1 })
    pure <| .local ((`local).appendIndexAfter idx)
  let proof := mkOfEqTrueCore e proof
  let size := (← get).newThms.size
  let gen ← getGeneration e
  -- TODO: we should have a flag for collecting all unary patterns in a local theorem
  if let some thm ← mkEMatchTheoremWithKind'? origin proof .fwd then
    activateTheorem thm gen
  if let some thm ← mkEMatchTheoremWithKind'? origin proof .bwd then
    activateTheorem thm gen
  if (← get).newThms.size == size then
    if let some thm ← mkEMatchTheoremWithKind'? origin proof .default then
      activateTheorem thm gen
  if (← get).newThms.size == size then
    reportIssue m!"failed to create E-match local theorem for{indentExpr e}"

def propagateForallPropDown (e : Expr) : GoalM Unit := do
  let .forallE n a b bi := e | return ()
  if (← isEqFalse e) then
    if b.hasLooseBVars then
      let α := a
      let p := b
      -- `e` is of the form `∀ x : α, p x`
      -- Add fact `∃ x : α, ¬ p x`
      let u ← getLevel α
      let prop := mkApp2 (mkConst ``Exists [u]) α (mkLambda n bi α (mkNot p))
      let proof := mkApp3 (mkConst ``Grind.of_forall_eq_false [u]) α (mkLambda n bi α p) (← mkEqFalseProof e)
      addNewFact proof prop (← getGeneration e)
    else
      let h ← mkEqFalseProof e
      pushEqTrue a <| mkApp3 (mkConst ``Grind.eq_true_of_imp_eq_false) a b h
      pushEqFalse b <| mkApp3 (mkConst ``Grind.eq_false_of_imp_eq_false) a b h
  else if (← isEqTrue e) then
    if let some (e', h') ← eqResolution e then
      trace_goal[grind.eqResolution] "{e}, {e'}"
      let h := mkOfEqTrueCore e (← mkEqTrueProof e)
      let h' := mkApp h' h
      addNewFact h' e' (← getGeneration e)
    else
      if b.hasLooseBVars then
        addLocalEMatchTheorems e

end Lean.Meta.Grind
