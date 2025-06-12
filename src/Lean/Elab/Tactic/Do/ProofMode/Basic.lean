/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Sebastian Graf
-/
prelude
import Lean.Meta
import Std.Tactic.Do.Syntax
import Lean.Elab.Tactic.Do.ProofMode.MGoal

namespace Lean.Elab.Tactic.Do.ProofMode
open Std.Do
open Lean Elab.Tactic Meta

structure MStartResult where
  goal : MGoal
  proof? : Option Expr := none

def mStart (goal : Expr) : MetaM MStartResult := do
  -- check if already in proof mode
  if let some mgoal := parseMGoal? goal then
    return { goal := mgoal }

  let listType := mkApp (mkConst ``List [.succ .zero]) (mkSort (.succ .zero))
  let σs ← mkFreshExprMVar listType
  let P ← mkFreshExprMVar (mkApp (mkConst ``SPred) σs)
  let inst ← synthInstance (mkApp3 (mkConst ``PropAsSPredTautology) goal σs P)
  let prf := mkApp4 (mkConst ``ProofMode.start_entails) σs P goal inst
  let goal : MGoal := { σs,  hyps := emptyHyp σs, target := ← instantiateMVars P }
  return { goal, proof? := some prf }

def mStartMVar (mvar : MVarId) : MetaM (MVarId × MGoal) := mvar.withContext do
  let goal ← instantiateMVars <| ← mvar.getType
  unless ← isProp goal do
    throwError "type mismatch\n{← mkHasTypeButIsExpectedMsg (← inferType goal) (mkSort .zero)}"

  let result ← mStart goal
  if let some proof := result.proof? then
    let subgoal ←
      mkFreshExprSyntheticOpaqueMVar result.goal.toExpr (← mvar.getTag)
    mvar.assign (mkApp proof subgoal)
    return (subgoal.mvarId!, result.goal)
  else
    return (mvar, result.goal)

@[builtin_tactic Lean.Parser.Tactic.mstart]
def elabMStart : Tactic | _ => do
  let (mvar, _) ← mStartMVar (← getMainGoal)
  replaceMainGoal [mvar]

@[builtin_tactic Lean.Parser.Tactic.mstop]
def elabMStop : Tactic | _ => do
  -- parse goal
  let mvar ← getMainGoal
  mvar.withContext do
  let goal ← instantiateMVars <| ← mvar.getType

  -- check if already in proof mode
  let some mgoal := parseMGoal? goal | throwError "not in proof mode"
  mvar.setType mgoal.strip
