/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Meta.KAbstract
import Init.Lean.Meta.Tactic.Util

namespace Lean
namespace Meta

def generalize (mvarId : MVarId) (e : Expr) (x : Name) : MetaM MVarId := do
withMVarContext mvarId $ do
  checkNotAssigned mvarId `generalize;
  tag ← getMVarTag mvarId;
  target ← getMVarType mvarId;
  target ← instantiateMVars target;
  targetAbst ← kabstract target e;
  unless targetAbst.hasLooseBVars $
    throwTacticEx `generalize mvarId ("failed to find expression in the target");
  eType ← inferType e;
  let targetNew := Lean.mkForall x BinderInfo.default eType targetAbst;
  unlessM (isTypeCorrect targetNew) $
    throwTacticEx `generalize mvarId ("result is not type correct");
  mvarNew ← mkFreshExprSyntheticOpaqueMVar targetNew tag;
  assignExprMVar mvarId (mkApp mvarNew e);
  pure mvarNew.mvarId!

end Meta
end Lean
