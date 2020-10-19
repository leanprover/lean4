#lang lean4
/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.InferType
import Lean.Meta.LevelDefEq

/-
This is not the Kernel type checker, but an auxiliary method for checking
whether terms produced by tactics and `isDefEq` are type correct.
-/

namespace Lean.Meta

private def ensureType (e : Expr) : MetaM Unit := do
getLevel e
pure ()

def throwLetTypeMismatchMessage {α} (fvarId : FVarId) : MetaM α := do
let lctx ← getLCtx
match lctx.find? fvarId with
| some (LocalDecl.ldecl _ _ n t v _) => do
  let vType ← inferType v
  throwError! "invalid let declaration, term{indentExpr v}\nhas type{indentExpr vType}\nbut is expected to have type{indentExpr t}"
| _ => unreachable!

@[specialize] private def checkLambdaLet
    (check   : Expr → MetaM Unit)
    (e : Expr) : MetaM Unit :=
lambdaLetTelescope e fun xs b => do
  xs.forM fun x => do
    let xDecl ← getFVarLocalDecl x;
    match xDecl with
    | LocalDecl.cdecl _ _ _ t _ =>
      ensureType t
      check t
    | LocalDecl.ldecl _ _ _ t v _ =>
      ensureType t
      check t
      let vType ← inferType v
      unless (← isDefEq t vType) do throwLetTypeMismatchMessage x.fvarId!
      check v
  check b

@[specialize] private def checkForall
    (check   : Expr → MetaM Unit)
    (e : Expr) : MetaM Unit :=
forallTelescope e fun xs b => do
  xs.forM fun x => do
    let xDecl ← getFVarLocalDecl x
    ensureType xDecl.type
    check xDecl.type
  ensureType b
  check b

private def checkConstant (constName : Name) (us : List Level) : MetaM Unit := do
let cinfo ← getConstInfo constName
unless us.length == cinfo.lparams.length do
  throwIncorrectNumberOfLevels constName us

private def getFunctionDomain (f : Expr) : MetaM Expr := do
let fType ← inferType f
let fType ← whnfD fType
match fType with
| Expr.forallE _ d _ _ => pure d
| _                    => throwFunctionExpected f

def throwAppTypeMismatch {α} {m} [Monad m] [MonadExceptOf Exception m] [Ref m] [AddErrorMessageContext m] [MonadLiftT MetaM m]
    (f a : Expr) (extraMsg : MessageData := Format.nil) : m α := do
let e := mkApp f a
let aType ← inferType a
let expectedType ← liftM $ getFunctionDomain f
throwError! "application type mismatch{indentExpr e}\nargument{indentExpr a}\nhas type{indentExpr aType}\nbut is expected to have type{indentExpr expectedType}{extraMsg}"

@[specialize] private def checkApp
    (check   : Expr → MetaM Unit)
    (f a : Expr) : MetaM Unit := do
check f
check a
let fType ← inferType f
let fType ← whnf fType
match fType with
| Expr.forallE _ d _ _ =>
  let aType ← inferType a
  unless (← isDefEq d aType) do
    throwAppTypeMismatch f a
| _ => throwFunctionExpected (mkApp f a)

private partial def checkAux : Expr → MetaM Unit
| e@(Expr.forallE ..)  => checkForall checkAux e
| e@(Expr.lam ..)      => checkLambdaLet checkAux e
| e@(Expr.letE ..)     => checkLambdaLet checkAux e
| Expr.const c lvls _  => checkConstant c lvls
| Expr.app f a _       => checkApp checkAux f a
| Expr.mdata _ e _     => checkAux e
| Expr.proj _ _ e _    => checkAux e
| _                    => pure ()

def check (e : Expr) : MetaM Unit :=
traceCtx `Meta.check $
  withTransparency TransparencyMode.all $ checkAux e

def isTypeCorrect (e : Expr) : MetaM Bool := do
try
  check e
  pure true
catch ex =>
  trace[Meta.typeError]! ex.toMessageData
  pure false

initialize
  registerTraceClass `Meta.check
  registerTraceClass `Meta.typeError

end Lean.Meta
