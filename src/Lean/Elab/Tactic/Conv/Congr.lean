/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Simp.Main
import Lean.Elab.Tactic.Conv.Basic

namespace Lean.Elab.Tactic.Conv
open Meta

@[builtinTactic Lean.Parser.Tactic.Conv.congr] def evalCongr : Tactic := fun stx => do
   withMainContext do
     let (lhs, rhs) ← getLhsRhs
     unless lhs.isApp do
       throwError "invalid 'congr' conv tactic, application expected{indentD lhs}"
     lhs.withApp fun f args => do
      let infos := (← getFunInfoNArgs f args.size).paramInfo
      let mut r := { expr := f : Simp.Result }
      let mut newGoals := #[]
      let mut i := 0
      for arg in args do
        trace[Debug.Meta.Tactic.simp] "app [{i}] {infos.size} {arg} hasFwdDeps: {infos[i].hasFwdDeps}"
        let addGoal ←
          if i < infos.size && !infos[i].hasFwdDeps then
            pure true
          else
            pure (← whnfD (← inferType r.expr)).isArrow
        if addGoal then
          let (rhs, newGoal) ← mkConvGoalFor arg
          newGoals := newGoals.push newGoal.mvarId!
          r ← Simp.mkCongr r { expr := rhs, proof? := newGoal }
        else
          r ← Simp.mkCongrFun r arg
        i := i + 1
      let proof ← r.getProof
      assignExprMVar rhs.mvarId! r.expr
      assignExprMVar (← getMainGoal) proof
      replaceMainGoal newGoals.toList

end Lean.Elab.Tactic.Conv
