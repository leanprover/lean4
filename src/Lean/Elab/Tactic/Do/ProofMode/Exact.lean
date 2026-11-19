/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Sebastian Graf
-/
module

prelude
public import Lean.Elab.Tactic.Do.ProofMode.Basic
public import Lean.Elab.Tactic.Do.ProofMode.Focus
public import Lean.Elab.Tactic.ElabTerm

public section

namespace Lean.Elab.Tactic.Do.ProofMode
open Std.Do SPred.Tactic
open Lean Elab Tactic Meta

def _root_.Lean.Elab.Tactic.Do.ProofMode.MGoal.exact (goal : MGoal) (hyp : Syntax) : OptionT MetaM Expr := do
  if goal.findHyp? hyp.getId |>.isNone then failure
  let focusRes ← goal.focusHypWithInfo ⟨hyp⟩
  OptionT.mk do
  let proof := mkApp5 (mkConst ``Exact.assumption [goal.u]) goal.σs goal.hyps focusRes.restHyps goal.target focusRes.proof
  unless ← isDefEq focusRes.focusHyp goal.target do
    throwError "mexact tactic failed, hypothesis {hyp} is not definitionally equal to {goal.target}"
  return proof

def _root_.Lean.Elab.Tactic.Do.ProofMode.MGoal.exactPure (goal : MGoal) (hyp : Syntax) : TacticM Expr := do
  let φ ← mkFreshExprMVar (mkSort .zero)
  let h ← elabTermEnsuringType hyp φ
  let P ← mkFreshExprMVar (mkApp (mkConst ``SPred [goal.u]) goal.σs)
  let some inst ← synthInstance? (mkApp3 (mkConst ``PropAsSPredTautology [goal.u]) φ goal.σs P)
    | throwError "mexact tactic failed, {hyp} is not an SPred tautology"
  return mkApp6 (mkConst ``Exact.from_tautology [goal.u]) goal.σs φ goal.hyps goal.target inst h

@[builtin_tactic Lean.Parser.Tactic.mexact]
def elabMExact : Tactic
  | `(tactic| mexact $hyp:term) => do
    let mvar ← getMainGoal
    mvar.withContext do
      let g ← instantiateMVars <| ← mvar.getType
      let some goal := parseMGoal? g | throwError "not in proof mode"
      if let some prf ← liftMetaM (goal.exact hyp) then
    mvar.assign prf
      else
        mvar.assign (← goal.exactPure hyp)
      replaceMainGoal []
  | _ => throwUnsupportedSyntax
