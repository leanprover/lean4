/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Sebastian Graf
-/
prelude
import Std.Tactic.Do.Syntax
import Lean.Elab.Tactic.Do.ProofMode.Focus
import Lean.Elab.Tactic.Do.ProofMode.Basic
import Lean.Elab.Tactic.Do.ProofMode.Pure
import Lean.Elab.Tactic.Do.ProofMode.Intro

namespace Lean.Elab.Tactic.Do.ProofMode
open Std.Do Lean.Parser.Tactic
open Lean Elab Tactic Meta

initialize registerTraceClass `Meta.Tactic.Do.cases

theorem SCases.add_goal {σs} {P Q H T : SPred σs} (hand : Q ∧ H ⊣⊢ₛ P) (hgoal : P ⊢ₛ T) : Q ∧ H ⊢ₛ T :=
  hand.mp.trans hgoal

theorem SCases.clear {σs} {Q H T : SPred σs} (hgoal : Q ∧ ⌜True⌝ ⊢ₛ T) : Q ∧ H ⊢ₛ T :=
  (SPred.and_mono_r SPred.true_intro).trans hgoal

theorem SCases.pure {σs} {Q T : SPred σs} (hgoal : Q ∧ ⌜True⌝ ⊢ₛ T) : Q ⊢ₛ T :=
  (SPred.and_intro .rfl SPred.true_intro).trans hgoal

theorem SCases.and_1 {σs} {Q H₁' H₂' H₁₂' T : SPred σs} (hand : H₁' ∧ H₂' ⊣⊢ₛ H₁₂') (hgoal : Q ∧ H₁₂' ⊢ₛ T) : (Q ∧ H₁') ∧ H₂' ⊢ₛ T :=
  ((SPred.and_congr_r hand.symm).trans SPred.and_assoc.symm).mpr.trans hgoal

theorem SCases.and_2 {σs} {Q H₁' H₂ T : SPred σs} (hgoal : (Q ∧ H₁') ∧ H₂ ⊢ₛ T) : (Q ∧ H₂) ∧ H₁' ⊢ₛ T :=
  SPred.and_right_comm.mp.trans hgoal

theorem SCases.and_3 {σs} {Q H₁ H₂ H T : SPred σs} (hand : H ⊣⊢ₛ H₁ ∧ H₂) (hgoal : (Q ∧ H₂) ∧ H₁ ⊢ₛ T) : Q ∧ H ⊢ₛ T :=
  (SPred.and_congr_r hand).mp.trans (SPred.and_assoc.mpr.trans (SPred.and_right_comm.mp.trans hgoal))

theorem SCases.exists {σs : List Type} {Q : SPred σs} {ψ : α → SPred σs} {T : SPred σs}
  (h : ∀ a, Q ∧ ψ a ⊢ₛ T) : Q ∧ (∃ a, ψ a) ⊢ₛ T :=
    SPred.imp_elim' (SPred.exists_elim fun a => SPred.imp_intro (SPred.entails.trans SPred.and_symm (h a)))

class IsAnd {σs : List Type} (P : SPred σs) (Q₁ Q₂ : outParam (SPred σs)) where to_and : P ⊣⊢ₛ Q₁ ∧ Q₂
instance (σs) (Q₁ Q₂ : SPred σs) : IsAnd (σs:=σs) spred(Q₁ ∧ Q₂) Q₁ Q₂ where to_and := .rfl
instance (σs) : IsAnd (σs:=σs) ⌜p ∧ q⌝ ⌜p⌝ ⌜q⌝ where to_and := SPred.pure_and.symm
instance (σs) (P Q₁ Q₂ : σ → SPred σs) [base : ∀ s, IsAnd (P s) (Q₁ s) (Q₂ s)] : IsAnd (σs:=σ::σs) P Q₁ Q₂ where to_and := fun s => (base s).to_and

-- Given σs and H, produces H₁, H₂ and a proof that H₁ ∧ H₂ ⊣⊢ₛ H.
def synthIsAnd (σs H : Expr) : OptionT MetaM (Expr × Expr × Expr) := do
  if let some (_σs, H₁, H₂) := parseAnd? H.consumeMData then
    return (H₁, H₂, mkApp2 (mkConst ``SPred.bientails.refl) σs H)
  try
    let H₁ ← mkFreshExprMVar (mkApp (mkConst ``SPred) σs)
    let H₂ ← mkFreshExprMVar (mkApp (mkConst ``SPred) σs)
    let inst ← synthInstance (mkApp4 (mkConst ``IsAnd) σs H H₁ H₂)
    return (H₁, H₂, mkApp5 (mkConst ``IsAnd.to_and) σs H H₁ H₂ inst)
  catch _ => failure

-- Produce a proof for Q ∧ H ⊢ₛ T by opening a new goal P ⊢ₛ T, where P ⊣⊢ₛ Q ∧ H.
def mCasesAddGoal (goals : IO.Ref (Array MVarId)) (σs : Expr) (T : Expr) (Q : Expr) (H : Expr) : MetaM (Unit × MGoal × Expr) := do
  let (P, hand) := mkAnd σs Q H
  -- hand : Q ∧ H ⊣⊢ₛ P
  -- Need to produce a proof that P ⊢ₛ T and return res
  let goal : MGoal := { σs := σs, hyps := P, target := T }
  let m ← mkFreshExprSyntheticOpaqueMVar goal.toExpr
  goals.modify (·.push m.mvarId!)
  let prf := mkApp7 (mkConst ``SCases.add_goal) σs P Q H T hand m
  let goal := { goal with hyps := mkAnd! σs Q H }
  return ((), goal, prf)

private def getQH (goal : MGoal) : MetaM (Expr × Expr) := do
  let some (_, Q, H) := parseAnd? goal.hyps | throwError m!"Internal error: Hypotheses not a conjunction {goal.hyps}"
  return (Q, H)

-- Pretty much like sPureCore, but for existential quantifiers.
-- This function receives the hypothesis H=(∃ (x : α), ψ x) to destruct.
-- It will provide a proof for Q ∧ H ⊢ₛ T
-- if `k` produces a proof for Q ∧ ψ n ⊢ₛ T that may range over `name : α`.
-- It calls `k` with name.
def mCasesExists (H : Expr) (name : TSyntax ``binderIdent)
  (k : Expr /-name:α-/ → MetaM (α × MGoal × Expr)) : MetaM (α × MGoal × Expr) := do
  let some (α, σs, ψ) := H.consumeMData.app3? ``SPred.exists | throwError "Not an existential quantifier {H}"
  let (name, ref) ← getFreshHypName name
  withLocalDeclD name α fun x => do
    addLocalVarInfo ref (← getLCtx) x α
    let (r, goal, prf /- : goal.toExpr -/) ← k x
    let (Q, _) ← getQH goal
    let u ← getLevel α
    let prf := mkApp6 (mkConst ``SCases.exists [u]) α σs Q ψ goal.target (← mkLambdaFVars #[x] prf)
    let goal := { goal with hyps := mkAnd! σs Q H }
    return (r, goal, prf)

-- goal is P ⊢ₛ T
-- The caller focuses on hypothesis H, P ⊣⊢ₛ Q ∧ H.
-- scasesCore on H, pat and k builds H ⊢ₛ H' according to pat, then calls k with H'
-- k knows context Q and builds goal Q ∧ H' ⊢ₛ T and a proof of the goal.
-- (k should not also apply H ⊢ₛ H' or unfocus because that does not work with spureCore which needs the see `P'` and not `Q ∧ _`.)
-- then scasesCore builds a proof for Q ∧ H ⊢ₛ T from P' ⊢ₛ T:
--   Q ∧ H ⊢ₛ Q ∧ H' ⊢ₛ P' ⊢ₛ T
-- and finally the caller builds the proof for
--   P ⊢ₛ Q ∧ H ⊢ₛ T
-- by unfocussing.
partial def mCasesCore (σs : Expr) (H : Expr) (pat : MCasesPat) (k : Expr → MetaM (α × MGoal × Expr)): MetaM (α × MGoal × Expr) :=
  match pat with
  | .clear => do
    let H' := emptyHyp σs -- H' = ⌜True⌝
    let (a, goal, prf) ← k H'
    let (Q, _H) ← getQH goal
    -- prf : Q ∧ ⌜True⌝ ⊢ₛ T
    -- Then Q ∧ H ⊢ₛ Q ∧ ⌜True⌝ ⊢ₛ T
    let prf := mkApp5 (mkConst ``SCases.clear) σs Q H goal.target prf
    let goal := { goal with hyps := mkAnd! σs Q H }
    return (a, goal, prf)
  | .stateful name => do
    let (name, ref) ← getFreshHypName name
    let uniq ← mkFreshId
    let hyp := Hyp.mk name uniq H.consumeMData
    addHypInfo ref σs hyp (isBinder := true)
    k hyp.toExpr
  | .pure name => do
    mPureCore σs H name fun _ _hφ => do
      -- This case is very similar to the clear case, but we need to
      -- return Q ⊢ₛ T, not Q ∧ H ⊢ₛ T.
      let H' := emptyHyp σs -- H' = ⌜True⌝
      let (a, goal, prf) ← k H'
      let (Q, _H) ← getQH goal
      -- prf : Q ∧ ⌜True⌝ ⊢ₛ T
      -- Then Q ⊢ₛ Q ∧ ⌜True⌝ ⊢ₛ T
      let prf := mkApp4 (mkConst ``SCases.pure) σs Q goal.target prf
      let goal := { goal with hyps := Q }
      return (a, goal, prf)
    -- Now prf : Q ∧ H ⊢ₛ T (where H is ⌜φ⌝). Exactly what is needed.
  | .one name => do
    try
      -- First try to see if H can be introduced as a pure hypothesis
      let φ ← mkFreshExprMVar (mkSort .zero)
      let _ ← synthInstance (mkApp3 (mkConst ``IsPure) σs H φ)
      mCasesCore σs H (.pure name) k
    catch _ =>
      -- Otherwise introduce it as a stateful hypothesis.
      mCasesCore σs H (.stateful name) k
  | .tuple [] => mCasesCore σs H .clear k
  | .tuple [p] => mCasesCore σs H p k
  | .tuple (p :: ps) => do
    if let some (H₁, H₂, hand) ← synthIsAnd σs H then
      -- goal is Q ∧ H ⊢ₛ T, where `hand : H ⊣⊢ₛ H₁ ∧ H₂`. Plan:
      -- 1. Recurse on H₁ and H₂.
      -- 2. The inner callback sees H₁' and H₂' and calls k on H₁₂', where H₁₂' = mkAnd H₁' H₂'
      -- 3. The inner callback receives P' ⊢ₛ T, where (P' ⊣⊢ₛ Q ∧ H₁₂').
      -- 4. The inner callback returns (Q ∧ H₁') ∧ H₂' ⊢ₛ T
      -- 5. The outer callback receives (Q ∧ H₁') ∧ H₂ ⊢ₛ T
      -- 6. The outer callback reassociates and returns (Q ∧ H₂) ∧ H₁' ⊢ₛ T
      -- 7. The top-level receives (Q ∧ H₂) ∧ H₁ ⊢ₛ T
      -- 8. Reassociate to Q ∧ (H₁ ∧ H₂) ⊢ₛ T, rebuild Q ∧ H ⊢ₛ T and return it.
      let ((a, Q), goal, prf) ← mCasesCore σs H₁ p fun H₁' => do
        let ((a, Q), goal, prf) ← mCasesCore σs H₂ (.tuple ps) fun H₂' => do
          let (H₁₂', hand') := mkAnd σs H₁' H₂'
          let (a, goal, prf) ← k H₁₂' -- (2)
          -- (3) prf : Q ∧ H₁₂' ⊢ₛ T
          -- (4) refocus to (Q ∧ H₁') ∧ H₂'
          let (Q, _H) ← getQH goal
          let T := goal.target
          let prf := mkApp8 (mkConst ``SCases.and_1) σs Q H₁' H₂' H₁₂' T hand' prf
          -- check prf
          let QH₁' := mkAnd! σs Q H₁'
          let goal := { goal with hyps := mkAnd! σs QH₁' H₂' }
          return ((a, Q), goal, prf)
        -- (5) prf : (Q ∧ H₁') ∧ H₂ ⊢ₛ T
        -- (6) refocus to prf : (Q ∧ H₂) ∧ H₁' ⊢ₛ T
        let prf := mkApp6 (mkConst ``SCases.and_2) σs Q H₁' H₂ goal.target prf
        let QH₂ := mkAnd! σs Q H₂
        let goal := { goal with hyps := mkAnd! σs QH₂ H₁' }
        return ((a, Q), goal, prf)
      -- (7) prf : (Q ∧ H₂) ∧ H₁ ⊢ₛ T
      -- (8) rearrange to Q ∧ H ⊢ₛ T
      let prf := mkApp8 (mkConst ``SCases.and_3) σs Q H₁ H₂ H goal.target hand prf
      let goal := { goal with hyps := mkAnd! σs Q H }
      return (a, goal, prf)
    else if let some (_α, σs, ψ) := H.consumeMData.app3? ``SPred.exists then
      let .one n := p
        | throwError "cannot further destruct a term after moving it to the Lean context"
      -- goal is Q ∧ (∃ x, ψ x) ⊢ₛ T. The plan is pretty similar to sPureCore:
      -- 1. Recurse on ψ n where (n : α) is named according to the head pattern p.
      -- 2. Receive a proof for Q ∧ ψ n ⊢ₛ T.
      -- 3. Build a proof for Q ∧ (∃ x, ψ x) ⊢ₛ T from it (in sCasesExists).
      mCasesExists H n fun x => mCasesCore σs (ψ.betaRev #[x]) (.alts ps) k
    else throwError "Neither a conjunction nor an existential quantifier {H}"
  | .alts [] => throwUnsupportedSyntax
  | .alts [p] => mCasesCore σs H p k
  | .alts (p :: ps) => do
    let some (σs, H₁, H₂) := H.consumeMData.app3? ``SPred.or | throwError "Not a disjunction {H}"
    -- goal is Q ∧ (H₁ ∨ H₂) ⊢ₛ T. Plan:
    -- 1. Recurse on H₁ and H₂ with the same k.
    -- 2. Receive proofs for Q ∧ H₁ ⊢ₛ T and Q ∧ H₂ ⊢ₛ T.
    -- 3. Build a proof for Q ∧ (H₁ ∨ H₂) ⊢ₛ T from them.
    let (_a, goal₁,  prf₁) ← mCasesCore σs H₁ p k
    let (a,  _goal₂, prf₂) ← mCasesCore σs H₂ (.alts ps) k
    let (Q, _H₁) ← getQH goal₁
    let goal := { goal₁ with hyps := mkAnd! σs Q (mkApp3 (mkConst ``SPred.or) σs H₁ H₂) }
    let prf := mkApp7 (mkConst ``SPred.and_or_elim_r) σs Q H₁ H₂ goal.target prf₁ prf₂
    return (a, goal, prf)

private theorem assembled_proof {σs} {P P' Q H H' T : SPred σs}
  (hfocus : P ⊣⊢ₛ Q ∧ H) (hcases : H ⊢ₛ H') (hand : Q ∧ H' ⊣⊢ₛ P') (hprf₃ : P' ⊢ₛ T) : P ⊢ₛ T :=
  hfocus.mp.trans ((SPred.and_mono_r hcases).trans (hand.mp.trans hprf₃))

private theorem blah2 {σs} {P Q H R : SPred σs}
  (h₁ : P ⊣⊢ₛ Q ∧ H) (h₂ : Q ∧ H ⊢ₛ R) : P ⊢ₛ R :=
  h₁.mp.trans h₂

private theorem blah3 {σs} {P Q H T : SPred σs}
  (hand : Q ∧ H ⊣⊢ₛ P) (hgoal : P ⊢ₛ T) : Q ∧ H ⊢ₛ T :=
  hand.mp.trans hgoal

@[builtin_tactic Lean.Parser.Tactic.mcases]
def elabMCases : Tactic
  | `(tactic| mcases $hyp:ident with $pat:mcasesPat) => do
  let pat ← liftMacroM <| MCasesPat.parse pat
  let (mvar, goal) ← mStartMVar (← getMainGoal)
  mvar.withContext do

  let focus ← goal.focusHypWithInfo hyp
  -- goal : P ⊢ₛ T,
  -- hfocus : P ⊣⊢ₛ Q ∧ H
  let Q := focus.restHyps
  let H := focus.focusHyp
  let goals ← IO.mkRef #[]
  let (_, _new_goal, prf) ← mCasesCore goal.σs H pat (mCasesAddGoal goals goal.σs goal.target Q)

  -- Now prf : Q ∧ H ⊢ₛ T. Prepend hfocus.mp, done.
  let prf := focus.rewriteHyps goal prf
  -- check prf
  mvar.assign prf
  replaceMainGoal (← goals.get).toList
  | _ => throwUnsupportedSyntax
