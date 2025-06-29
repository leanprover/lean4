/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Sebastian Graf
-/
prelude
import Std.Tactic.Do.Syntax
import Lean.Elab.Tactic.Do.ProofMode.MGoal

namespace Lean.Elab.Tactic.Do.ProofMode
open Std.Do
open Lean Elab Tactic Meta

def mLeftRightCore (right : Bool) (mvar : MVarId) : MetaM MVarId := do
  let g ← instantiateMVars <| ← mvar.getType
  let some goal := parseMGoal? g | throwError "not in proof mode"

  let mkApp3 (.const ``SPred.or []) σs L R := goal.target | throwError "target is not SPred.or"

  let (thm, keep) := if right then (``SPred.or_intro_r', R) else (``SPred.or_intro_l', L)

  let newGoal ← mkFreshExprSyntheticOpaqueMVar {goal with target := keep}.toExpr
  mvar.assign (mkApp5 (mkConst thm) σs goal.hyps L R newGoal)
  return newGoal.mvarId!

@[builtin_tactic Lean.Parser.Tactic.mleft]
def elabMLeft : Tactic | _ => do
  let mvar ← getMainGoal
  mvar.withContext do
  let newGoal ← mLeftRightCore (right := false) mvar
  replaceMainGoal [newGoal]

@[builtin_tactic Lean.Parser.Tactic.mright]
def elabMRight : Tactic | _ => do
  let mvar ← getMainGoal
  mvar.withContext do
  let newGoal ← mLeftRightCore (right := true) mvar
  replaceMainGoal [newGoal]
