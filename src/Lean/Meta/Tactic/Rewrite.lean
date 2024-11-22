/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.AppBuilder
import Lean.Meta.MatchUtil
import Lean.Meta.KAbstract
import Lean.Meta.Check
import Lean.Meta.Tactic.Util
import Lean.Meta.Tactic.Apply

namespace Lean.Meta

structure RewriteResult where
  eNew     : Expr
  eqProof  : Expr
  mvarIds  : List MVarId -- new goals

/--
Rewrite goal `mvarId`
-/
def _root_.Lean.MVarId.rewrite (mvarId : MVarId) (e : Expr) (heq : Expr)
    (symm : Bool := false) (config := { : Rewrite.Config }) : MetaM RewriteResult :=
  mvarId.withContext do
    mvarId.checkNotAssigned `rewrite
    let heqIn := heq
    let heqType ← instantiateMVars (← inferType heq)
    let (newMVars, binderInfos, heqType) ← forallMetaTelescopeReducing heqType
    let heq := mkAppN heq newMVars
    let cont (heq heqType : Expr) : MetaM RewriteResult := do
      match (← matchEq? heqType) with
      | none => throwTacticEx `rewrite mvarId m!"equality or iff proof expected{indentExpr heqType}"
      | some (α, lhs, rhs) =>
        let cont (heq heqType lhs rhs : Expr) : MetaM RewriteResult := do
          if lhs.getAppFn.isMVar then
            throwTacticEx `rewrite mvarId m!"pattern is a metavariable{indentExpr lhs}\nfrom equation{indentExpr heqType}"
          let e ← instantiateMVars e
          let eAbst ← withConfig (fun oldConfig => { config, oldConfig with }) <| kabstract e lhs config.occs
          unless eAbst.hasLooseBVars do
            throwTacticEx `rewrite mvarId m!"did not find instance of the pattern in the target expression{indentExpr lhs}"
          -- construct rewrite proof
          let eNew := eAbst.instantiate1 rhs
          let eNew ← instantiateMVars eNew
          let eType ← inferType e
          let motive := Lean.mkLambda `_a BinderInfo.default α eAbst
          try
            check motive
          catch ex =>
            throwTacticEx `rewrite mvarId m!"\
              motive is not type correct\
              \n\n\
              Explanation: The rewrite tactic rewrites an expression 'e' using an equality 'a = b' in the following way. \
              First, it looks for all 'a' in 'e'. Second, it tries to abstract these occurrences of 'a' to create a function 'm' with the property that 'e = m a'. \
              Third, we observe that '{.ofConstName ``congrArg}' implies that `m a = m b`. Thus, if the goal was 'e', it suffices to prove 'm b' using '{.ofConstName ``Eq.mpr}'. \
              This function 'm' is called the *motive*. If 'e' depends on specific properties of 'a', then the motive might not typecheck.\n\n\
              Type-incorrect motive:{indentD motive}\nError: {ex.toMessageData}"
          unless (← withLocalDeclD `_a α fun a => do isDefEq (← inferType (eAbst.instantiate1 a)) eType) do
            -- NB: using motive.arrow? would disallow motives where the dependency
            -- can be reduced away
            throwTacticEx `rewrite mvarId m!"motive is dependent{indentD motive}"
          let u1 ← getLevel α
          let u2 ← getLevel eType
          let eqPrf := mkApp6 (.const ``congrArg [u1, u2]) α eType lhs rhs motive heq
          postprocessAppMVars `rewrite mvarId newMVars binderInfos
            (synthAssignedInstances := !tactic.skipAssignedInstances.get (← getOptions))
          let newMVarIds ← newMVars.map Expr.mvarId! |>.filterM fun mvarId => not <$> mvarId.isAssigned
          let otherMVarIds ← getMVarsNoDelayed heqIn
          let otherMVarIds := otherMVarIds.filter (!newMVarIds.contains ·)
          let newMVarIds := newMVarIds ++ otherMVarIds
          pure { eNew := eNew, eqProof := eqPrf, mvarIds := newMVarIds.toList }
        match symm with
        | false => cont heq heqType lhs rhs
        | true  => do
          let heq ← mkEqSymm heq
          let heqType ← mkEq rhs lhs
          cont heq heqType rhs lhs
    match heqType.iff? with
    | some (lhs, rhs) =>
      let heqType ← mkEq lhs rhs
      let heq := mkApp3 (mkConst `propext) lhs rhs heq
      cont heq heqType
    | none =>
      cont heq heqType

end Lean.Meta
