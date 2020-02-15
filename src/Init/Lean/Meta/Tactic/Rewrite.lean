/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Meta.AppBuilder
import Init.Lean.Meta.KAbstract
import Init.Lean.Meta.Check
import Init.Lean.Meta.Tactic.Apply

namespace Lean
namespace Meta

structure RewriteResult :=
(eNew     : Expr)
(eqPrf    : Expr)
(newGoals : List MVarId)

def rewriteCore (mvarId : MVarId) (e : Expr) (heq : Expr) (symm : Bool := false) (occs : Occurrences := Occurrences.all) : MetaM RewriteResult :=
withMVarContext mvarId $ do
  checkNotAssigned mvarId `rewrite;
  heqType ← inferType heq;
  (newMVars, binderInfos, heqType) ← forallMetaTelescopeReducing heqType;
  let heq := mkAppN heq newMVars;
  let continue (heq heqType : Expr) : MetaM RewriteResult :=
    match heqType.eq? with
    | none => throwTacticEx `rewrite mvarId ("equality of iff proof expected")
    | some (α, lhs, rhs) =>
      let continue (heq heqType lhs rhs : Expr) : MetaM RewriteResult := do {
        when lhs.getAppFn.isMVar $
          throwTacticEx `rewrite mvarId ("pattern is a metavariable");
        e ← instantiateMVars e;
        eAbst ← kabstract e lhs occs;
        unless eAbst.hasLooseBVars $
          throwTacticEx `rewrite mvarId ("did not find instance of the pattern in the target expression");
        -- construct rewrite proof
        let eNew := eAbst.instantiate1 rhs;
        eNew ← instantiateMVars eNew;
        eEqE ← mkEq e e;
        let eEqEAbst := mkApp eEqE.appFn! eAbst;
        let motive := Lean.mkLambda `_a BinderInfo.default α eEqEAbst;
        unlessM (isTypeCorrect motive) $
          throwTacticEx `rewrite mvarId ("motive is not type correct");
        eqRefl ← mkEqRefl e;
        eqPrf ← mkEqNDRec motive eqRefl heq;
        postprocessAppMVars `rewrite mvarId newMVars binderInfos;
        newMVars ← newMVars.filterM $ fun mvar => not <$> isExprMVarAssigned mvar.mvarId!;
        pure { eNew := eNew, eqPrf := eqPrf, newGoals := newMVars.toList.map Expr.mvarId! }
      };
      match symm with
      | false => continue heq heqType lhs rhs
      | true  => do {
        heq ← mkEqSymm heq;
        heqType ← mkEq rhs lhs;
        continue heq heqType rhs lhs
      };
  match heqType.iff? with
  | some (lhs, rhs) => do
    heqType ← mkEq lhs rhs;
    let heq := mkApp3 (mkConst `propext) lhs rhs heq;
    continue heq heqType
  | none =>
    continue heq heqType

end Meta
end Lean
