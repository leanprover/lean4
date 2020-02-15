/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Meta.AppBuilder
import Init.Lean.Meta.Tactic.Util
import Init.Lean.Meta.Tactic.Assert
import Init.Lean.Meta.Tactic.Intro
import Init.Lean.Meta.Tactic.Clear

namespace Lean
namespace Meta

def replaceLocalDecl (mvarId : MVarId) (fvarId : FVarId) (newType : Expr) (eqProof : Expr) : MetaM (FVarId × MVarId) := do
withMVarContext mvarId $ do
  localDecl ← getLocalDecl fvarId;
  newTypePr ← mkEqMP eqProof (mkFVar fvarId);
  mvarId ← assert mvarId localDecl.userName newType newTypePr;
  (fvarIdNew, mvarId) ← intro1 mvarId;
  (do mvarId ← clear mvarId fvarId; pure (fvarIdNew, mvarId)) <|> pure (fvarIdNew, mvarId)

end Meta
end Lean
