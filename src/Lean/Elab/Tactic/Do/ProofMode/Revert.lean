/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Sebastian Graf
-/
module

prelude
public import Std.Tactic.Do.Syntax
public import Lean.Elab.Tactic.Do.ProofMode.Focus
public import Lean.Elab.Tactic.Do.ProofMode.Basic

public section

namespace Lean.Elab.Tactic.Do.ProofMode
open Std.Do SPred.Tactic
open Lean Elab Tactic Meta

partial def mRevertStep (goal : MGoal) (ref : TSyntax `ident) (k : MGoal → MetaM Expr) : MetaM Expr := do
  let res ← goal.focusHypWithInfo ref
  let P := goal.hyps
  let Q := res.restHyps
  let H := res.focusHyp
  let T := goal.target
  let prf ← k { goal with hyps := Q, target := mkApp3 (mkConst ``SPred.imp [goal.u]) goal.σs H T }
  let prf := mkApp7 (mkConst ``Revert.revert [goal.u]) goal.σs P Q H T res.proof prf
  return prf

@[builtin_tactic Lean.Parser.Tactic.mrevert]
def elabMRevert : Tactic
  | `(tactic| mrevert $h) => do
  let (mvar, goal) ← mStartMVar (← getMainGoal)
  mvar.withContext do

  let goals ← IO.mkRef []
  mvar.assign (← mRevertStep goal h fun newGoal => do
    let m ← mkFreshExprSyntheticOpaqueMVar newGoal.toExpr
    goals.modify (m.mvarId! :: ·)
    return m)
  replaceMainGoal (← goals.get)
  | _ => throwUnsupportedSyntax
