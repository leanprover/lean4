/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
prelude
import Std.Tactic.Do.Syntax
import Lean.Elab.Tactic.Do.ProofMode.Basic
import Lean.Elab.Tactic.Do.ProofMode.Exact
import Lean.Elab.Tactic.Do.ProofMode.Focus

namespace Lean.Elab.Tactic.Do.ProofMode
open Std.Do
open Lean Elab Tactic Meta

theorem Assumption.assumption_l {σs : List Type} {P Q R : SPred σs} (h : P ⊢ₛ R) : P ∧ Q ⊢ₛ R :=
  SPred.and_elim_l.trans h
theorem Assumption.assumption_r {σs : List Type} {P Q R : SPred σs} (h : Q ⊢ₛ R) : P ∧ Q ⊢ₛ R :=
  SPred.and_elim_r.trans h

partial def MGoal.assumption (goal : MGoal) : OptionT MetaM Expr := do
  if let some _ := parseEmptyHyp? goal.hyps then
    failure
  if let some hyp := parseHyp? goal.hyps then
    guard (← isDefEq hyp.p goal.target)
    return mkApp2 (mkConst ``SPred.entails.refl) goal.σs hyp.p
  if let some (σs, lhs, rhs) := parseAnd? goal.hyps then
    -- NB: Need to prefer rhs over lhs, like the goal view (Lean.Elab.Tactic.Do.ProofMode.Display).
    mkApp5 (mkConst ``Assumption.assumption_r) σs lhs rhs goal.target <$> assumption { goal with hyps := rhs }
    <|>
    mkApp5 (mkConst ``Assumption.assumption_l) σs lhs rhs goal.target <$> assumption { goal with hyps := lhs }
  else
    panic! s!"assumption: hypothesis without proper metadata: {goal.hyps}"

def MGoal.assumptionPure (goal : MGoal) : OptionT MetaM Expr := do
  let φ := mkApp2 (mkConst ``SPred.tautological) goal.σs goal.target
  let fvarId ← OptionT.mk (findLocalDeclWithType? φ)
  let inst ← synthInstance? (mkApp3 (mkConst ``PropAsSPredTautology) φ goal.σs goal.target)
  return mkApp6 (mkConst ``Exact.from_tautology) φ goal.σs goal.hyps goal.target inst (.fvar fvarId)

@[builtin_tactic Lean.Parser.Tactic.massumption]
def elabMAssumption : Tactic | _ => do
  let mvar ← getMainGoal
  mvar.withContext do
  let g ← instantiateMVars <| ← mvar.getType
  let some goal := parseMGoal? g | throwError "not in proof mode"

  let some proof ← liftMetaM <|
    goal.assumption <|> goal.assumptionPure
    | throwError "hypothesis not found"
  mvar.assign proof
  replaceMainGoal []
