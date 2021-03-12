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
  discard <| getLevel e

def throwLetTypeMismatchMessage {α} (fvarId : FVarId) : MetaM α := do
  let lctx ← getLCtx
  match lctx.find? fvarId with
  | some (LocalDecl.ldecl _ _ n t v _) => do
    let vType ← inferType v
    throwError "invalid let declaration, term{indentExpr v}\nhas type{indentExpr vType}\nbut is expected to have type{indentExpr t}"
  | _ => unreachable!

private def checkConstant (constName : Name) (us : List Level) : MetaM Unit := do
  let cinfo ← getConstInfo constName
  unless us.length == cinfo.levelParams.length do
    throwIncorrectNumberOfLevels constName us

private def getFunctionDomain (f : Expr) : MetaM (Expr × BinderInfo) := do
  let fType ← inferType f
  let fType ← whnfD fType
  match fType with
  | Expr.forallE _ d _ c => return (d, c.binderInfo)
  | _                    => throwFunctionExpected f

/-
Given to expressions `a` and `b`, this method tries to annotate terms with `pp.explicit := true` to
expose "implicit" differences. For example, suppose `a` and `b` are of the form
```lean
@HashMap Nat Nat eqInst hasInst1
@HashMap Nat Nat eqInst hasInst2
```
By default, the pretty printer formats both of them as `HashMap Nat Nat`.
So, counterintuitive error messages such as
```lean
error: application type mismatch
  HashMap.insert m
argument
  m
has type
  HashMap Nat Nat
but is expected to have type
  HashMap Nat Nat
```
would be produced.
By adding `pp.explicit := true`, we can generate the more informative error
```lean
error: application type mismatch
  HashMap.insert m
argument
  m
has type
  @HashMap Nat Nat eqInst hasInst1
but is expected to have type
  @HashMap Nat Nat eqInst hasInst2
```
Remark: this method implements a simple heuristic, we should extend it as we find other counterintuitive
error messages.
-/
partial def addPPExplicitToExposeDiff (a b : Expr) : MetaM (Expr × Expr) := do
  if (← getOptions).getBool `pp.all false || (← getOptions).getBool `pp.explicit false then
    return (a, b)
  else
    visit a b
where
  visit (a b : Expr) : MetaM (Expr × Expr) := do
    try
      if !a.isApp || !b.isApp then
        return (a, b)
      else if a.getAppNumArgs != b.getAppNumArgs then
        return (a, b)
      else if not (← isDefEq a.getAppFn b.getAppFn) then
        return (a, b)
      else
        let fType ← inferType a.getAppFn
        forallBoundedTelescope fType a.getAppNumArgs fun xs _ => do
          let mut as := a.getAppArgs
          let mut bs := b.getAppArgs
          if (← hasExplicitDiff xs as bs) then
            return (a, b)
          else
            for i in [:as.size] do
              let (ai, bi) ← visit as[i] bs[i]
              as := as.set! i ai
              bs := bs.set! i bi
            let a := mkAppN a.getAppFn as
            let b := mkAppN b.getAppFn bs
            return (a.setAppPPExplicit, b.setAppPPExplicit)
    catch _ =>
      return (a, b)

  hasExplicitDiff (xs as bs : Array Expr) : MetaM Bool := do
    for i in [:xs.size] do
      let localDecl ← getLocalDecl xs[i].fvarId!
      if localDecl.binderInfo.isExplicit then
         if not (← isDefEq as[i] bs[i]) then
           return true
    return false

/-
  Return error message "has type{givenType}\nbut is expected to have type{expectedType}"
-/
def mkHasTypeButIsExpectedMsg (givenType expectedType : Expr) : MetaM MessageData := do
  try
    let givenTypeType ← inferType givenType
    let expectedTypeType ← inferType expectedType
    let (givenType, expectedType) ← addPPExplicitToExposeDiff givenType expectedType
    let (givenTypeType, expectedTypeType) ← addPPExplicitToExposeDiff givenTypeType expectedTypeType
    m!"has type{indentD m!"{givenType} : {givenTypeType}"}\nbut is expected to have type{indentD m!"{expectedType} : {expectedTypeType}"}"
  catch _ =>
    let (givenType, expectedType) ← addPPExplicitToExposeDiff givenType expectedType
    m!"has type{indentExpr givenType}\nbut is expected to have type{indentExpr expectedType}"

def throwAppTypeMismatch {α} (f a : Expr) (extraMsg : MessageData := Format.nil) : MetaM α := do
  let (expectedType, binfo) ← getFunctionDomain f
  let mut e := mkApp f a
  unless binfo.isExplicit do
    e := e.setAppPPExplicit
  let aType ← inferType a
  throwError "application type mismatch{indentExpr e}\nargument{indentExpr a}\n{← mkHasTypeButIsExpectedMsg aType expectedType}"

def checkApp (f a : Expr) : MetaM Unit := do
  let fType ← inferType f
  let fType ← whnf fType
  match fType with
  | Expr.forallE _ d _ _ =>
    let aType ← inferType a
    unless (← isDefEq d aType) do
      throwAppTypeMismatch f a
  | _ => throwFunctionExpected (mkApp f a)

private partial def checkAux : Expr → MetaM Unit
  | e@(Expr.forallE ..)  => checkForall e
  | e@(Expr.lam ..)      => checkLambdaLet e
  | e@(Expr.letE ..)     => checkLambdaLet e
  | Expr.const c lvls _  => checkConstant c lvls
  | Expr.app f a _       => do checkAux f; checkAux a; checkApp f a
  | Expr.mdata _ e _     => checkAux e
  | Expr.proj _ _ e _    => checkAux e
  | _                    => pure ()
where
  checkLambdaLet (e : Expr) : MetaM Unit :=
    lambdaLetTelescope e fun xs b => do
      xs.forM fun x => do
        let xDecl ← getFVarLocalDecl x;
        match xDecl with
        | LocalDecl.cdecl (type := t) .. =>
          ensureType t
          checkAux t
        | LocalDecl.ldecl (type := t) (value := v) .. =>
          ensureType t
          checkAux t
          let vType ← inferType v
          unless (← isDefEq t vType) do throwLetTypeMismatchMessage x.fvarId!
          checkAux v
      checkAux b

  checkForall (e : Expr) : MetaM Unit :=
    forallTelescope e fun xs b => do
      xs.forM fun x => do
        let xDecl ← getFVarLocalDecl x
        ensureType xDecl.type
        checkAux xDecl.type
      ensureType b
      checkAux b

def check (e : Expr) : MetaM Unit :=
  traceCtx `Meta.check do
    withTransparency TransparencyMode.all $ checkAux e

def isTypeCorrect (e : Expr) : MetaM Bool := do
  try
    check e
    pure true
  catch ex =>
    trace[Meta.typeError] ex.toMessageData
    pure false

builtin_initialize
  registerTraceClass `Meta.check
  registerTraceClass `Meta.typeError

end Lean.Meta
