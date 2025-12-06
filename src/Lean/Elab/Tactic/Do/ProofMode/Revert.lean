/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Sebastian Graf
-/
module

prelude
public import Lean.Elab.Tactic.Do.ProofMode.Focus
public import Lean.Elab.Tactic.Do.ProofMode.Basic

public section

namespace Lean.Elab.Tactic.Do.ProofMode
open Std.Do SPred.Tactic
open Lean Elab Tactic Meta

variable {m : Type → Type u} [Monad m] [MonadControlT MetaM m] [MonadLiftT MetaM m]

partial def mRevert (goal : MGoal) (ref : TSyntax `ident) (k : MGoal → m Expr) : m Expr := do
  let res ← goal.focusHypWithInfo ref
  let P := goal.hyps
  let Q := res.restHyps
  let H := res.focusHyp
  let T := goal.target
  let prf ← k { goal with hyps := Q, target := mkApp3 (mkConst ``SPred.imp [goal.u]) goal.σs H T }
  let prf := mkApp7 (mkConst ``Revert.revert [goal.u]) goal.σs P Q H T res.proof prf
  return prf

/--
Turn goal
  hᵢ : Hᵢ
  ⊢ₛ T e₁ ... eₙ
into
  hᵢ : fun sₙ ... s₁ => Hᵢ
  h : fun sₙ ... s₁ => ⌜s₁ = e₁ ∧ ... ∧ sₙ = eₙ⌝
  ⊢ₛ T
-/
partial def mRevertForallN (goal : MGoal) (n : Nat) (hypName : Name) (k : MGoal → m Expr) : m Expr := do
  if n = 0 then return ← k goal
  let H := goal.hyps
  let T := goal.target.consumeMData
  let f := T.getAppFn
  let args := T.getAppRevArgs
  let revertArgs := args[0:n].toArray.reverse
  unless revertArgs.size = n do
    liftMetaM <| throwError "mrevert: expected {n} excess arguments in {T}, got {revertArgs.size}"
  let revertArgsTypes ← liftMetaM <| revertArgs.mapM inferType

  let declInfos ← revertArgsTypes.mapIdxM fun i ty => do
    return ((← liftMetaM <| mkFreshUserName `s).appendIndexAfter (i+1), ty)

  -- Build `fun s₁ ... sₙ => H ∧ ⌜s₁ = e₁ ∧ ... ∧ sₙ = eₙ⌝`
  let (H, φ) ← withLocalDeclsDND declInfos fun ss => do
    let eqs ← (revertArgs.zip ss).mapM fun (e, s) => mkEq s e
    let eqs := eqs.toList
    let φ := mkAndN eqs
    let φ := SPred.mkPure goal.u goal.σs φ
    let uniq ← liftMetaM <| mkFreshUserName hypName
    let φ := Hyp.toExpr ⟨hypName, uniq, ← mkLambdaFVars ss φ⟩
    return (← mkLambdaFVars ss H, φ)

  -- Build `⟨rfl, ..., rfl⟩ : e₁ = e₁ ∧ ... ∧ eₙ = eₙ`
  let prfs ← liftMetaM <| revertArgs.mapM mkEqRefl
  let h ← mkAndIntroN prfs.toList

  -- Push `fun s₁ ... sₙ =>` into the hyps in `H`
  let u := goal.u
  let σs' := revertArgsTypes.foldr (TypeList.mkCons u) goal.σs
  let H ← instantiateMVarsIfMVarApp H
  let H := pushForallContextIntoHyps σs' H
  let (H, hand) := SPred.mkAnd u σs' H φ

  -- Prove `((fun s₁ ... sₙ => H) ∧ (fun s₁ ... sₙ => ⌜s₁ = e₁ ∧ ... ∧ sₙ = eₙ⌝)) ⊢ₛ T`
  let goal' := { u, σs := σs', hyps := H, target := mkAppRev f args[n:] }
  let prf ← k goal'

  -- Build the proof for `H ⊢ₛ T e₁ ... eₙ`
  let prf := mkApp8 (mkConst ``Revert.and_pure_intro_r [goal.u]) goal.σs (← inferType h) goal.hyps (mkAppN H revertArgs) goal.target h (mkAppN hand revertArgs) (mkAppN prf revertArgs)
  -- goal.checkProof prf
  return prf

@[builtin_tactic Lean.Parser.Tactic.mrevert]
def elabMRevert : Tactic
  | `(tactic| mrevert $h:ident) => do
  let mvar ← getMainGoal
  let some goal := parseMGoal? (← mvar.getType)
    | throwError "Not in proof mode"
  mvar.withContext do
  let goals ← IO.mkRef []
  mvar.assign (← mRevert goal h fun newGoal => do
    let m ← mkFreshExprSyntheticOpaqueMVar newGoal.toExpr
    goals.modify (m.mvarId! :: ·)
    return m)
  replaceMainGoal (← goals.get)
  | `(tactic| mrevert ∀ $[$n]?) => do
  let (mvar, goal) ← mStartMainGoal
  mvar.withContext do
  let n := ((·.getNat) <$> n).getD 1
  let goals ← IO.mkRef []
  mvar.assign (← mRevertForallN goal n (← mkFreshUserName `h) fun newGoal => do
    let m ← mkFreshExprSyntheticOpaqueMVar newGoal.toExpr
    goals.modify (m.mvarId! :: ·)
    return m)
  replaceMainGoal (← goals.get)
  | _ => throwUnsupportedSyntax
