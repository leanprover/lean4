/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Meta.ExprDefEq
import Init.Lean.Meta.Tactic.Util

namespace Lean
namespace Meta

def assumptionAux (mvarId : MVarId) : MetaM Bool :=
withMVarContext mvarId $ do
  checkNotAssigned mvarId "assumption";
  mvarType ← getMVarType mvarId;
  lctx ← getLCtx;
  h? ← lctx.findDeclRevM $ fun decl => condM (isDefEq mvarType decl.type) (pure (some decl.toExpr)) (pure none);
  match h? with
  | some h => do assignExprMVar mvarId h; pure true
  | none   => pure false

def assumption (mvarId : MVarId) : MetaM Unit :=
unlessM (assumptionAux mvarId) $ throw $ Exception.other "`assumption` failed"

end Meta
end Lean
