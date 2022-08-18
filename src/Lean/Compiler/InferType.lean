/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.LCNFTypes
import Lean.Compiler.Util

namespace Lean.Compiler

class MonadInferType (m : Type → Type) where
  inferType : Expr → m Expr

namespace InferType

structure InferTypeM.Context where
  lctx : LocalContext

abbrev InferTypeM := ReaderT InferTypeM.Context CoreM

instance : MonadLCtx InferTypeM where
  getLCtx := return (← read).lctx

instance : AddMessageContext InferTypeM where
  addMessageContext msgData := do
    let env ← getEnv
    let lctx ← getLCtx
    let opts ← getOptions
    return MessageData.withContext { env, lctx, opts, mctx := {} } msgData

@[inline] def withLocalDeclImp (binderName : Name) (type : Expr) (binderInfo : BinderInfo) (k : Expr → InferTypeM α) : InferTypeM α := do
  let fvarId ← mkFreshFVarId
  withReader (fun ctx => { ctx with lctx := ctx.lctx.mkLocalDecl fvarId binderName type binderInfo }) do
    k (.fvar fvarId)

@[inline] def withLocalDecl [Monad m] [MonadControlT InferTypeM m] (binderName : Name) (type : Expr) (binderInfo : BinderInfo) (k : Expr → m α) : m α :=
  controlAt InferTypeM fun runInBase => withLocalDeclImp binderName type binderInfo fun x =>runInBase (k x)

def inferConstType (declName : Name) (us : List Level) : CoreM Expr :=
  if declName == ``lcAny || declName == ``lcErased then
    return anyTypeExpr
  else
    instantiateLCNFTypeLevelParams declName us

def inferFVarType (fvarId : FVarId) : InferTypeM Expr := do
  let some decl := (← getLCtx).find? fvarId | fvarId.throwUnknown
  return decl.type

def getCasesResultingType (casesInfo : CasesInfo) (cases : Expr) : InferTypeM Expr :=
  go (cases.getArg! casesInfo.motivePos) casesInfo.geNumDiscrs
where
  go (motive : Expr) (n : Nat) : InferTypeM Expr :=
    match n, motive with
    | 0,   _ => return motive
    | n+1, .lam _ _ b _ => go b n
    | _, _ => throwError "invalid LCNF cases-experession{indentExpr cases}"

mutual
  partial def inferAppType (e : Expr) : InferTypeM Expr := do
    if let some casesInfo ← isCasesApp? e then
      getCasesResultingType casesInfo e
    else
      let f := e.getAppFn
      let args := e.getAppArgs
      let mut j := 0
      let mut fType ← inferType f
      for i in [:args.size] do
        fType := fType.headBeta
        match fType with
        | .forallE _ _ b _ => fType := b
        | _ =>
          fType := fType.instantiateRevRange j i args |>.headBeta
          match fType with
          | .forallE _ _ b _ => j := i; fType := b
          | _ =>
            if fType.isAnyType then return anyTypeExpr
            throwError "function expected{indentExpr (mkAppN f args[:i])} : {fType}\nfunction type{indentExpr (← inferType f)}"
      return fType.instantiateRevRange j args.size args |>.headBeta

  partial def inferProjType (structName : Name) (idx : Nat) (s : Expr) : InferTypeM Expr := do
    let failed {α} : Unit → InferTypeM α := fun _ =>
      throwError "invalid projection{indentExpr (mkProj structName idx s)}"
    let structType ← inferType s
    matchConstStruct structType.getAppFn failed fun structVal structLvls ctorVal =>
      let n := structVal.numParams
      let structParams := structType.getAppArgs
      if n != structParams.size then
        failed ()
      else do
        let mut ctorType ← inferAppType (mkAppN (mkConst ctorVal.name structLvls) structParams)
        for _ in [:idx] do
          match ctorType with
          | .forallE _ _ body _ =>
            assert! !body.hasLooseBVars
            ctorType := body
          | _ =>
            if ctorType.isAnyType then return anyTypeExpr
            failed ()
        match ctorType with
        | .forallE _ d _ _ => return d
        | _ =>
          if ctorType.isAnyType then return anyTypeExpr
          failed ()

  partial def getLevel? (type : Expr) : InferTypeM (Option Level) := do
    match (← inferType type) with
    | .sort u => return some u
    | e =>
      if e.isAnyType then return none
      else
        throwError "type expected{indentExpr type}"

  partial def inferForallType (e : Expr) : InferTypeM Expr :=
    go e #[]
  where
    go (e : Expr) (fvars : Array Expr) : InferTypeM Expr := do
      match e with
      | .forallE n d b bi =>
        withLocalDecl n (d.instantiateRev fvars) bi fun fvar => go b (fvars.push fvar)
      | _ =>
        let e := e.instantiateRev fvars
        let some u ← getLevel? e | return anyTypeExpr
        let mut u := u
        for x in fvars do
          let xType ← inferType x
          let some v ← getLevel? xType | return anyTypeExpr
          u := .imax v u
        return .sort u.normalize

  partial def inferLambdaType (e : Expr) : InferTypeM Expr :=
    go e #[] #[]
  where
    go (e : Expr) (fvars : Array Expr) (all : Array Expr) : InferTypeM Expr := do
      match e with
      | .lam n d b bi =>
        withLocalDecl n (d.instantiateRev all) bi fun fvar => go b (fvars.push fvar) (all.push fvar)
      | .letE n t _ b _ =>
        withLocalDecl n (t.instantiateRev all) .default fun fvar => go b fvars (all.push fvar)
      | e =>
        let type ← inferType (e.instantiateRev all)
        return (← getLCtx).mkForall fvars type

  partial def inferType (e : Expr) : InferTypeM Expr :=
    match e with
    | .const c us    => inferConstType c us
    | .proj n i s    => inferProjType n i s
    | .app ..        => inferAppType e
    | .mvar ..       => throwError "unexpected metavariable {e}"
    | .fvar fvarId   => inferFVarType fvarId
    | .bvar ..       => throwError "unexpected bound variable {e}"
    | .mdata _ e     => inferType e
    | .lit v         => return v.type
    | .sort lvl      => return .sort (mkLevelSucc lvl)
    | .forallE ..    => inferForallType e
    | .lam ..        => inferLambdaType e
    | .letE ..       => inferLambdaType e
end

end InferType

instance : MonadInferType InferType.InferTypeM where
  inferType := InferType.inferType

export MonadInferType (inferType)

instance [MonadLift m n] [MonadInferType m] : MonadInferType n where
  inferType e := liftM (inferType e : m _)

def getLevel [Monad m] [MonadInferType m] [MonadError m] (type : Expr) : m Level := do
  match (← inferType type) with
  | .sort u => return u
  | e => if e.isAnyType then return levelOne else throwError "type expected{indentExpr type}"

/-- Create `lcUnreachable type` -/
def mkLcUnreachable [Monad m] [MonadInferType m] [MonadError m] (type : Expr) : m Expr := do
  let u ← getLevel type
  return .app (.const ``lcUnreachable [u]) type

/-- Create `lcCast expectedType e : expectedType` -/
def mkLcCast [Monad m] [MonadInferType m] [MonadError m] (e : Expr) (expectedType : Expr) : m Expr := do
  let type ← inferType e
  let u ← getLevel type
  let v ← getLevel expectedType
  return mkApp3 (.const ``lcCast [u, v]) type expectedType e

end Lean.Compiler