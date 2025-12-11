/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Sebastian Graf
-/
module

prelude
public import Std.Tactic.Do.Syntax
public import Lean.Elab.Tactic.Do.ProofMode.MGoal

public section

namespace Lean.Elab.Tactic.Do.ProofMode
open Std.Do SPred.Tactic
open Lean Elab.Tactic Meta

structure MStartResult where
  goal : MGoal
  proof? : Option Expr := none

def mStart (goal : Expr) : MetaM MStartResult := do
  -- check if already in proof mode
  if let some mgoal := parseMGoal? goal then
    return { goal := mgoal }

  let u ← mkFreshLevelMVar
  let σs ← mkFreshExprMVar (TypeList.mkType u)
  let P ← mkFreshExprMVar (mkApp (mkConst ``SPred [u]) σs)
  let inst ← synthInstance (mkApp3 (mkConst ``PropAsSPredTautology [u]) goal σs P)
  let u ← instantiateLevelMVars u
  let prf := mkApp4 (mkConst ``ProofMode.start_entails [u]) σs P goal inst
  let goal : MGoal := { u, σs, hyps := emptyHyp u σs, target := ← instantiateMVars P }
  return { goal, proof? := some prf }

def mStartMVar (mvar : MVarId) : MetaM (MVarId × MGoal) := mvar.withContext do
  let goal ← instantiateMVars <| ← mvar.getType
  unless ← isProp goal do
    throwError "The goal type of `{mkMVar mvar}` is not a proposition. It has type `{← inferType goal}`."

  let result ← mStart goal
  if let some proof := result.proof? then
    let subgoal ←
      mkFreshExprSyntheticOpaqueMVar result.goal.toExpr (← mvar.getTag)
    mvar.assign (mkApp proof subgoal)
    return (subgoal.mvarId!, result.goal)
  else
    return (mvar, result.goal)

def mStartMainGoal : TacticM (MVarId × MGoal) := do
  let (mvar, goal) ← mStartMVar (← getMainGoal)
  replaceMainGoal [mvar]
  return (mvar, goal)

@[builtin_tactic Lean.Parser.Tactic.mstart]
def elabMStart : Tactic | _ => discard mStartMainGoal

@[builtin_tactic Lean.Parser.Tactic.mstop]
def elabMStop : Tactic | _ => do
  -- parse goal
  let mvar ← getMainGoal
  mvar.withContext do
  let goal ← instantiateMVars <| ← mvar.getType

  -- check if already in proof mode
  let some mgoal := parseMGoal? goal | throwError "not in proof mode"
  mvar.setType mgoal.strip
