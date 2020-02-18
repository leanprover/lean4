/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.AuxRecursor
import Init.Lean.Util.WHNF
import Init.Lean.Meta.Basic
import Init.Lean.Meta.LevelDefEq

namespace Lean
namespace Meta

def isAuxDef? (constName : Name) : MetaM Bool := do
env ← getEnv; pure (isAuxRecursor env constName || isNoConfusion env constName)

def unfoldDefinition? (e : Expr) : MetaM (Option Expr)  :=
Lean.WHNF.unfoldDefinitionAux getConstNoEx isAuxDef? whnf inferType isExprDefEq synthPending getLocalDecl getExprMVarAssignment? e

def whnfCore (e : Expr) : MetaM Expr :=
Lean.WHNF.whnfCore getConstNoEx isAuxDef? whnf inferType isExprDefEqAux getLocalDecl getExprMVarAssignment? e

partial def whnfImpl : Expr → MetaM Expr
| e => Lean.WHNF.whnfEasyCases getLocalDecl getExprMVarAssignment? e $ fun e => do
  e ← whnfCore e;
  e? ← unfoldDefinition? e;
  match e? with
  | some e => whnfImpl e
  | none   => pure e

@[init] def setWHNFRef : IO Unit :=
whnfRef.set whnfImpl

/- Given an expression `e`, compute its WHNF and if the result is a constructor, return field #i. -/
def reduceProj? (e : Expr) (i : Nat) : MetaM (Option Expr) := do
env ← getEnv;
e   ← whnf e;
match e.getAppFn with
| Expr.const name _ _ =>
  match env.find? name with
  | some (ConstantInfo.ctorInfo ctorVal) =>
    let numArgs := e.getAppNumArgs;
    let idx := ctorVal.nparams + i;
    if idx < numArgs then
      pure (some (e.getArg! idx))
    else
      pure none
  | _ => pure none
| _ => pure none

end Meta
end Lean
