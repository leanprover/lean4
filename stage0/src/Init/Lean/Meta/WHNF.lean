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

unsafe def reduceNativeConst (α : Type) (typeName : Name) (constName : Name) : MetaM α := do
env ← getEnv;
match env.evalConstCheck α typeName constName with
| Except.error ex => throw $ Exception.other ex
| Except.ok v     => pure v

unsafe def reduceBoolNativeUnsafe (constName : Name) : MetaM Bool := reduceNativeConst Bool `Bool constName
unsafe def reduceNatNativeUnsafe (constName : Name) : MetaM Nat := reduceNativeConst Nat `Nat constName
@[implementedBy reduceBoolNativeUnsafe] constant reduceBoolNative (constName : Name) : MetaM Bool := arbitrary _
@[implementedBy reduceNatNativeUnsafe] constant reduceNatNative (constName : Name) : MetaM Nat := arbitrary _

def reduceNative? (e : Expr) : MetaM (Option Expr) :=
match e with
| Expr.app (Expr.const fName _ _) (Expr.const argName _ _) _ =>
  if fName == `Lean.reduceBool then do
    b ← reduceBoolNative argName;
    pure $ if b then some $ mkConst `Bool.true else some $ mkConst `Bool.false
  else if fName == `Lean.reduceNat then do
    n ← reduceNatNative argName;
    pure $ some $ mkNatLit n
  else
    pure none
| _ => pure none

partial def whnfImpl : Expr → MetaM Expr
| e => Lean.WHNF.whnfEasyCases getLocalDecl getExprMVarAssignment? e $ fun e => do
  e ← whnfCore e;
  v? ← reduceNative? e;
  match v? with
  | some v => pure v
  | none => do
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

@[specialize] private partial def whnfHeadPredAux (pred : Expr → MetaM Bool) : Expr → MetaM Expr
| e => Lean.WHNF.whnfEasyCases getLocalDecl getExprMVarAssignment? e $ fun e => do
  e ← whnfCore e;
  condM (pred e)
    (do
      e? ← unfoldDefinition? e;
      match e? with
      | some e => whnfHeadPredAux e
      | none   => pure e)
    (pure e)

def whnfHeadPred (e : Expr) (pred : Expr → MetaM Bool) : MetaM Expr :=
whnfHeadPredAux pred e

def whnfUntil (e : Expr) (declName : Name) : MetaM Expr :=
whnfHeadPredAux (fun e => pure $ e.isAppOf declName) e

def getStuckMVar? (e : Expr) : MetaM (Option MVarId) :=
WHNF.getStuckMVar? getConst whnf e

end Meta
end Lean
