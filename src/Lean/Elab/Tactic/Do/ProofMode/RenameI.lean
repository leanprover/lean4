/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Sebastian Graf
-/
module

prelude
public import Lean.Elab.Tactic.Do.ProofMode.Basic

namespace Lean.Elab.Tactic.Do.ProofMode
open Std.Do SPred.Tactic
open Lean Elab Tactic Meta

partial def mRenameI [Monad m] [MonadControlT MetaM m] [MonadLiftT MetaM m] (goal : MGoal)
    (idents : Array (TSyntax ``binderIdent)) (k : MGoal → m (α × Expr)) : m (α × Expr) := do
  let goal ← goal.renameInaccessibleHyps idents
  k goal

@[builtin_tactic Lean.Parser.Tactic.mrenameI]
def elabMRenameI : Tactic
  | `(tactic| mrename_i $idents:binderIdent*) => do
    let (mvar, goal) ← mStartMainGoal
    mvar.withContext do
    let goals ← IO.mkRef []
    mvar.assign (← Prod.snd <$> mRenameI goal idents fun newGoal => do
      let m ← mkFreshExprSyntheticOpaqueMVar newGoal.toExpr
      goals.modify (m.mvarId! :: ·)
      return ((), m))
    replaceMainGoal (← goals.get)
  | _ => throwUnsupportedSyntax
