/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.AuxRecursor
import Lean.Util.WHNF
import Lean.Meta.Basic
import Lean.Meta.LevelDefEq

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
| Except.error ex => throwError ex
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
    pure $ toExpr b
  else if fName == `Lean.reduceNat then do
    n ← reduceNatNative argName;
    pure $ toExpr n
  else
    pure none
| _ => pure none

@[inline] def withNatValue {α} (a : Expr) (k : Nat → MetaM (Option α)) : MetaM (Option α) := do
a ← whnf a;
match a with
| Expr.const `Nat.zero _ _      => k 0
| Expr.lit (Literal.natVal v) _ => k v
| _                             => pure none

def reduceUnaryNatOp (f : Nat → Nat) (a : Expr) : MetaM (Option Expr) :=
withNatValue a $ fun a =>
pure $ mkNatLit $ f a

def reduceBinNatOp (f : Nat → Nat → Nat) (a b : Expr) : MetaM (Option Expr) :=
withNatValue a $ fun a =>
withNatValue b $ fun b => do
trace `Meta.isDefEq.whnf.reduceBinOp $ fun _ => toString a ++ " op " ++ toString b;
pure $ mkNatLit $ f a b

def reduceBinNatPred (f : Nat → Nat → Bool) (a b : Expr) : MetaM (Option Expr) := do
withNatValue a $ fun a =>
withNatValue b $ fun b =>
pure $ toExpr $ f a b

def reduceNat? (e : Expr) : MetaM (Option Expr) :=
if e.hasFVar || e.hasMVar then
  pure none
else match e with
  | Expr.app (Expr.const fn _ _) a _                  =>
    if fn == `Nat.succ then reduceUnaryNatOp Nat.succ a
    else pure none
  | Expr.app (Expr.app (Expr.const fn _ _) a1 _) a2 _ =>
    if fn == `Nat.add then reduceBinNatOp Nat.add a1 a2
    else if fn == `Nat.sub then reduceBinNatOp Nat.sub a1 a2
    else if fn == `Nat.mul then reduceBinNatOp Nat.mul a1 a2
    else if fn == `Nat.div then reduceBinNatOp Nat.div a1 a2
    else if fn == `Nat.mod then reduceBinNatOp Nat.mod a1 a2
    else if fn == `Nat.beq then reduceBinNatPred Nat.beq a1 a2
    else if fn == `Nat.ble then reduceBinNatPred Nat.ble a1 a2
    else pure none
  | _ => pure none


@[inline] private def useWHNFCache (e : Expr) : MetaM Bool := do
-- We cache only closed terms
if e.hasFVar then pure false
else do
  ctx ← read;
  pure $ ctx.config.transparency != TransparencyMode.reducible

@[inline] private def cached? (useCache : Bool) (e : Expr) : MetaM (Option Expr) := do
if useCache then do
  ctx ← read;
  s   ← get;
  match ctx.config.transparency with
  | TransparencyMode.default => pure $ s.cache.whnfDefault.find? e
  | TransparencyMode.all     => pure $ s.cache.whnfAll.find? e
  | _                        => unreachable!
else
  pure none

private def cache (useCache : Bool) (e r : Expr) : MetaM Expr := do
ctx ← read;
when useCache $
  match ctx.config.transparency with
  | TransparencyMode.default => modify $ fun s => { s with cache := { s.cache with whnfDefault := s.cache.whnfDefault.insert e r } }
  | TransparencyMode.all     => modify $ fun s => { s with cache := { s.cache with whnfAll := s.cache.whnfAll.insert e r } }
  | _                        => unreachable!;
pure r

partial def whnfImpl : Expr → MetaM Expr
| e => Lean.WHNF.whnfEasyCases getLocalDecl getExprMVarAssignment? e $ fun e => do
  useCache ← useWHNFCache e;
  e? ← cached? useCache e;
  match e? with
  | some e' => pure e'
  | none    => do
    e' ← whnfCore e;
    v? ← reduceNat? e';
    match v? with
    | some v => cache useCache e v
    | none   => do
      v? ← reduceNative? e';
      match v? with
      | some v => cache useCache e v
      | none => do
        e? ← unfoldDefinition? e';
        match e? with
        | some e => whnfImpl e
        | none   => cache useCache e e'

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

def whnfUntil (e : Expr) (declName : Name) : MetaM (Option Expr) := do
e ← whnfHeadPredAux (fun e => pure $ !e.isAppOf declName) e;
if e.isAppOf declName then pure e
else pure none

def getStuckMVar? (e : Expr) : MetaM (Option MVarId) :=
WHNF.getStuckMVar? getConst whnf e

end Meta
end Lean
