/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.AuxRecursor
import Init.Lean.WHNF
import Init.Lean.Meta.Basic
import Init.Lean.Meta.LevelDefEq

namespace Lean
namespace Meta

def isAuxDef? (constName : Name) : MetaM Bool :=
do env ← getEnv; pure (isAuxRecursor env constName || isNoConfusion env constName)

@[specialize] def unfoldDefinitionAux {α}
    (e : Expr) (failK : MetaM α) (successK : Expr → MetaM α) : MetaM α :=
Lean.unfoldDefinitionAux getConstNoEx isAuxDef? whnf inferType isExprDefEq synthPending getLocalDecl
  getExprMVarAssignment e (fun _ => failK) successK

partial def whnfImpl : Expr → MetaM Expr
| e => whnfEasyCases getLocalDecl getExprMVarAssignment e $ fun e => do
  e ← whnfCore getConstNoEx isAuxDef? whnfImpl inferType isExprDefEqAux getLocalDecl getExprMVarAssignment e;
  Lean.unfoldDefinitionAux getConstNoEx isAuxDef? whnf inferType isExprDefEq synthPending getLocalDecl
    getExprMVarAssignment e (fun _ => pure e) whnfImpl

@[init] def setWHNFRef : IO Unit :=
whnfRef.set whnfImpl

end Meta
end Lean
