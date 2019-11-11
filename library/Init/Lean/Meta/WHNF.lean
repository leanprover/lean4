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

@[inline] private def getCachedWHNF (e : Expr) : MetaM (Option Expr) :=
do t ← getTransparency;
   s ← get;
   pure $ s.cache.whnf.find (t, e)

@[inline] private def cacheWHNF (e : Expr) (r : Expr) : MetaM Unit :=
do t ← getTransparency;
   modify $ fun s => { cache := { whnf := s.cache.whnf.insert (t, e) r, .. s.cache }, .. s }

@[specialize] partial def whnfAux
    (inferType         : Expr → MetaM Expr)
    (isDefEq           : Expr → Expr → MetaM Bool)
    (synthesizePending : Expr → MetaM Bool)
    : Expr → MetaM Expr
| e => whnfEasyCases getLocalDecl getExprMVarAssignment e $ fun e => do
  cached? ← getCachedWHNF e;
  match cached? with
  | some r => pure r
  | none   => do
    e ← whnfCore getConst isAuxDef? whnfAux inferType isDefEq getLocalDecl getExprMVarAssignment e;
    r ← unfoldDefinition getConst isAuxDef? whnfAux inferType isDefEq synthesizePending getLocalDecl
      getExprMVarAssignment e (fun _ => pure e) whnfAux;
    cacheWHNF e r;
    pure r

end Meta
end Lean
