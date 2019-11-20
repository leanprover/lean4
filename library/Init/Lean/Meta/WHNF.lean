/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.AuxRecursor
import Init.Lean.WHNF
import Init.Lean.Meta.Basic

namespace Lean
namespace Meta

private def isAuxDef? (constName : Name) : MetaM Bool :=
do env ← getEnv; pure (isAuxRecursor env constName || isNoConfusion env constName)

@[specialize] def unfoldDefinitionAux {α}
    (whnf              : Expr → MetaM Expr)
    (inferType         : Expr → MetaM Expr)
    (isDefEq           : Expr → Expr → MetaM Bool)
    (synthesizePending : Expr → MetaM Bool)
    (e : Expr)
    (failK : MetaM α) (successK : Expr → MetaM α) : MetaM α :=
Lean.unfoldDefinitionAux getConstNoEx isAuxDef? whnf inferType isDefEq synthesizePending getLocalDecl
  getExprMVarAssignment e (fun _ => failK) successK

@[specialize] partial def whnfAux
    (inferType         : Expr → MetaM Expr)
    (isDefEq           : Expr → Expr → MetaM Bool)
    (synthesizePending : Expr → MetaM Bool)
    : Expr → MetaM Expr
| e => whnfEasyCases getLocalDecl getExprMVarAssignment e $ fun e => do
  e ← whnfCore getConstNoEx isAuxDef? whnfAux inferType isDefEq getLocalDecl getExprMVarAssignment e;
  unfoldDefinitionAux whnfAux inferType isDefEq synthesizePending e (pure e) whnfAux

end Meta
end Lean
