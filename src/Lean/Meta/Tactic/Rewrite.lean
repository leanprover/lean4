/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.AppBuilder
import Lean.Meta.MatchUtil
import Lean.Meta.KAbstract
import Lean.Meta.Check
import Lean.Meta.Tactic.Apply

namespace Lean.Meta

structure RewriteResult :=
  (eNew     : Expr)
  (eqProof  : Expr)
  (mvarIds  : List MVarId) -- new goals

def rewrite (mvarId : MVarId) (e : Expr) (heq : Expr) (symm : Bool := false) (occs : Occurrences := Occurrences.all) : MetaM RewriteResult :=
  withMVarContext mvarId do
    checkNotAssigned mvarId `rewrite
    let heqType ← inferType heq
    let (newMVars, binderInfos, heqType) ← forallMetaTelescopeReducing heqType
    let heq := mkAppN heq newMVars
    let cont (heq heqType : Expr) : MetaM RewriteResult :=
      match (← matchEq? heqType) with
      | none => throwTacticEx `rewrite mvarId msg!"equality or iff proof expected{indentExpr heqType}"
      | some (α, lhs, rhs) =>
        let cont (heq heqType lhs rhs : Expr) : MetaM RewriteResult := do
          if lhs.getAppFn.isMVar then
            throwTacticEx `rewrite mvarId msg!"pattern is a metavariable{indentExpr lhs}\nfrom equation{indentExpr heqType}"
          let e ← instantiateMVars e
          let eAbst ← kabstract e lhs occs
          unless eAbst.hasLooseBVars do
            throwTacticEx `rewrite mvarId msg!"did not find instance of the pattern in the target expression{indentExpr lhs}"
          -- construct rewrite proof
          let eNew := eAbst.instantiate1 rhs
          let eNew ← instantiateMVars eNew
          let eEqE ← mkEq e e
          let eEqEAbst := mkApp eEqE.appFn! eAbst
          let motive := Lean.mkLambda `_a BinderInfo.default α eEqEAbst
          unless (← isTypeCorrect motive) do
            throwTacticEx `rewrite mvarId "motive is not type correct"
          let eqRefl ← mkEqRefl e
          let eqPrf ← mkEqNDRec motive eqRefl heq
          postprocessAppMVars `rewrite mvarId newMVars binderInfos
          let newMVars ← newMVars.filterM fun mvar => not <$> isExprMVarAssigned mvar.mvarId!
          pure { eNew := eNew, eqProof := eqPrf, mvarIds := newMVars.toList.map Expr.mvarId! }
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
