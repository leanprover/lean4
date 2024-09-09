/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.InferType

/-!
This is not the Kernel type checker, but an auxiliary method for checking
whether terms produced by tactics and `isDefEq` are type correct.
-/

namespace Lean.Meta

private def ensureType (e : Expr) : MetaM Unit := do
  discard <| getLevel e

def throwLetTypeMismatchMessage {α} (fvarId : FVarId) : MetaM α := do
  let lctx ← getLCtx
  match lctx.find? fvarId with
  | some (LocalDecl.ldecl _ _ _ t v _ _) => do
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
  | Expr.forallE _ d _ c => return (d, c)
  | _                    => throwFunctionExpected f

/--
Given two expressions `a` and `b`, this method tries to annotate terms with `pp.explicit := true` to
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
    -- Use a new metacontext depth to prevent isDefEq from unifying any metavariables.
    withNewMCtxDepth do visit (← instantiateMVars a) (← instantiateMVars b)
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
          if let some (as', bs') ← hasExplicitDiff? xs as bs then
            return (mkAppN a.getAppFn as', mkAppN b.getAppFn bs')
          else
            for i in [:as.size] do
              unless (← isDefEq as[i]! bs[i]!) do
                let (ai, bi) ← visit as[i]! bs[i]!
                as := as.set! i ai
                bs := bs.set! i bi
            let a := mkAppN a.getAppFn as
            let b := mkAppN b.getAppFn bs
            return (a.setAppPPExplicit, b.setAppPPExplicit)
    catch _ =>
      return (a, b)

  hasExplicitDiff? (xs as bs : Array Expr) : MetaM (Option (Array Expr × Array Expr)) := do
    for i in [:xs.size] do
      let localDecl ← xs[i]!.fvarId!.getDecl
      if localDecl.binderInfo.isExplicit then
         unless (← isDefEq as[i]! bs[i]!) do
           let (ai, bi) ← visit as[i]! bs[i]!
           return some (as.set! i ai, bs.set! i bi)
    return none

/--
  Return error message "has type{givenType}\nbut is expected to have type{expectedType}"
-/
def mkHasTypeButIsExpectedMsg (givenType expectedType : Expr) : MetaM MessageData := do
  try
    let givenTypeType ← inferType givenType
    let expectedTypeType ← inferType expectedType
    let (givenType, expectedType) ← addPPExplicitToExposeDiff givenType expectedType
    let (givenTypeType, expectedTypeType) ← addPPExplicitToExposeDiff givenTypeType expectedTypeType
    return m!"has type{indentD m!"{givenType} : {givenTypeType}"}\nbut is expected to have type{indentD m!"{expectedType} : {expectedTypeType}"}"
  catch _ =>
    let (givenType, expectedType) ← addPPExplicitToExposeDiff givenType expectedType
    return m!"has type{indentExpr givenType}\nbut is expected to have type{indentExpr expectedType}"

def throwAppTypeMismatch (f a : Expr) : MetaM α := do
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

private partial def checkAux (e : Expr) : MetaM Unit := do
  check e |>.run
where
  check (e : Expr) : MonadCacheT ExprStructEq Unit MetaM Unit :=
    checkCache { val := e : ExprStructEq } fun _ => do
      match e with
      | .forallE ..      => checkForall e
      | .lam ..          => checkLambdaLet e
      | .letE ..         => checkLambdaLet e
      | .const c lvls    => checkConstant c lvls
      | .app f a         => check f; check a; checkApp f a
      | .mdata _ e       => check e
      | .proj _ _ e      => check e
      | _                => return ()

  checkLambdaLet (e : Expr) : MonadCacheT ExprStructEq Unit MetaM Unit :=
    lambdaLetTelescope e fun xs b => do
      xs.forM fun x => do
        let xDecl ← getFVarLocalDecl x;
        match xDecl with
        | .cdecl (type := t) .. =>
          ensureType t
          check t
        | .ldecl (type := t) (value := v) .. =>
          ensureType t
          check t
          let vType ← inferType v
          unless (← isDefEq t vType) do throwLetTypeMismatchMessage x.fvarId!
          check v
      check b

  checkForall (e : Expr) : MonadCacheT ExprStructEq Unit MetaM Unit :=
    forallTelescope e fun xs b => do
      xs.forM fun x => do
        let xDecl ← getFVarLocalDecl x
        ensureType xDecl.type
        check xDecl.type
      ensureType b
      check b

/--
Throw an exception if `e` is not type correct.
-/
def check (e : Expr) : MetaM Unit :=
  withTraceNode `Meta.check (fun res =>
      return m!"{if res.isOk then checkEmoji else crossEmoji} {e}") do
    try
      withTransparency TransparencyMode.all $ checkAux e
    catch ex =>
      trace[Meta.check] ex.toMessageData
      throw ex

/--
Return true if `e` is type correct.
-/
def isTypeCorrect (e : Expr) : MetaM Bool := do
  try
    check e
    pure true
  catch _ =>
    pure false

builtin_initialize
  registerTraceClass `Meta.check

end Lean.Meta
