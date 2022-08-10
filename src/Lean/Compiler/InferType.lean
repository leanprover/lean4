/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.LCNFTypes

namespace Lean.Compiler.New -- TODO: remove .New

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

def inferConstType (declName : Name) (us : List Level) : CoreM Expr :=
  instantiateLCNFTypeLevelParams declName us

def inferFVarType (fvarId : FVarId) : InferTypeM Expr := do
  let some decl := (← getLCtx).find? fvarId | fvarId.throwUnknown
  return decl.type

mutual
  partial def inferAppType (f : Expr) (args : Array Expr) : InferTypeM Expr := do
    -- TODO: `casesOn` and `matcher` special support
    -- In LCNF, we want to represent them as `resulting type`, `discriminants`, `alternatives`
    let mut fType ← inferType f
    for _ in [:args.size] do
      match fType with
      | .forallE _ _ b _ => fType := b
      | _ =>
        if fType.isAnyType then return anyTypeExpr
        throwError "function expected{indentExpr f}"
    return fType.instantiateRev args

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
        let mut ctorType ← inferAppType (mkConst ctorVal.name structLvls) structParams
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
        let d := d.instantiateRev fvars
        let fvarId ← mkFreshFVarId
        withReader (fun ctx => { ctx with lctx := ctx.lctx.mkLocalDecl fvarId n d bi }) do
          go b (fvars.push (.fvar fvarId))
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
        let d := d.instantiateRev all
        let fvarId ← mkFreshFVarId
        let fvar := .fvar fvarId
        withReader (fun ctx => { ctx with lctx := ctx.lctx.mkLocalDecl fvarId n d bi }) do
          go b (fvars.push fvar) (all.push fvar)
      | .letE n t _ b _ =>
        let type := t.instantiateRev all
        let fvarId ← mkFreshFVarId
        let fvar := .fvar fvarId
        withReader (fun ctx => { ctx with lctx := ctx.lctx.mkLocalDecl fvarId n type .default }) do
          go b fvars (all.push fvar)
      | e =>
        let type ← inferType (e.instantiateRev all)
        return (← getLCtx).mkForall fvars type

  partial def inferType (e : Expr) : InferTypeM Expr :=
    match e with
    | .const c us    => inferConstType c us
    | .proj n i s    => inferProjType n i s
    | .app f ..      => inferAppType f.getAppFn e.getAppArgs
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