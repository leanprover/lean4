/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.LCNF.CompilerM
import Lean.Compiler.LCNF.Types

namespace Lean.Compiler.LCNF

namespace InferType

/--
We use a regular local context to store temporary local declarations
created during type inference.
-/
abbrev InferTypeM := ReaderT LocalContext CompilerM

def getLocalDecl (fvarId : FVarId) : InferTypeM LocalDecl := do
  match (← read).find? fvarId with
  | some localDecl => return localDecl
  | none => LCNF.getLocalDecl fvarId

def mkForallFVars (xs : Array Expr) (type : Expr) : InferTypeM Expr :=
  let b := type.abstract xs
  xs.size.foldRevM (init := b) fun i b => do
    let x := xs[i]!
    let .cdecl _ _ n ty _ ← getLocalDecl x.fvarId! | unreachable!
    let ty := ty.abstractRange i xs;
    return .forallE n ty b .default

def mkForallParams (params : Array Param) (type : Expr) : InferTypeM Expr :=
  let xs := params.map fun p => .fvar p.fvarId
  mkForallFVars xs type |>.run {}

@[inline] def withLocalDecl (binderName : Name) (type : Expr) (binderInfo : BinderInfo) (k : Expr → InferTypeM α) : InferTypeM α := do
  let fvarId ← mkFreshFVarId
  withReader (fun lctx => lctx.mkLocalDecl fvarId binderName type binderInfo) do
    k (.fvar fvarId)

def inferFVarType (fvarId : FVarId) : InferTypeM Expr :=
  return (← getLocalDecl fvarId).type

def inferConstType (declName : Name) (us : List Level) : CoreM Expr :=
  if declName == ``lcAny || declName == ``lcErased then
    return anyTypeExpr
  else
    instantiateLCNFTypeLevelParams declName us

mutual

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

  partial def inferAppTypeCore (f : Expr) (args : Array Expr) : InferTypeM Expr := do
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

  partial def inferAppType (e : Expr) : InferTypeM Expr := do
    inferAppTypeCore e.getAppFn e.getAppArgs

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
      if e.isAnyType then
        return none
      else
        throwError "type expected{indentExpr type}"

  partial def inferForallType (e : Expr) : InferTypeM Expr :=
    go e #[]
  where
    go (e : Expr) (fvars : Array Expr) : InferTypeM Expr := do
      match e with
      | .forallE n d b bi =>
        withLocalDecl n (d.instantiateRev fvars) bi fun fvar =>
          go b (fvars.push fvar)
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
        mkForallFVars fvars type

end
end InferType

def inferType (e : Expr) : CompilerM Expr :=
  InferType.inferType e |>.run {}

def getLevel (type : Expr) : CompilerM Level := do
  match (← inferType type) with
  | .sort u => return u
  | e => if e.isAnyType then return levelOne else throwError "type expected{indentExpr type}"

/-- Create `lcCast expectedType e : expectedType` -/
def mkLcCast (e : Expr) (expectedType : Expr) : CompilerM Expr := do
  let type ← inferType e
  let u ← getLevel type
  let v ← getLevel expectedType
  return mkApp3 (.const ``lcCast [u, v]) type expectedType e

def Code.inferType (code : Code) : CompilerM Expr := do
  match code with
  | .let _ k | .fun _ k | .jp _ k => k.inferType
  | .return fvarId => return (← getLocalDecl fvarId).type
  | .jmp fvarId args => InferType.inferAppTypeCore (.fvar fvarId) args |>.run {}
  | .unreach type => return type
  | .cases c => return c.resultType

def Code.inferParamType (params : Array Param) (code : Code) : CompilerM Expr := do
  let type ← code.inferType
  let xs := params.map fun p => .fvar p.fvarId
  InferType.mkForallFVars xs type |>.run {}

def AltCore.inferType (alt : Alt) : CompilerM Expr :=
  alt.getCode.inferType

def mkAuxLetDecl (e : Expr) (prefixName := `_x) : CompilerM Expr := do
  if e.isFVar then
    return e
  else
    let letDecl ← mkLetDecl (← mkFreshBinderName prefixName) (← inferType e) e
    return .fvar letDecl.fvarId

def mkForallParams (params : Array Param) (type : Expr) : CompilerM Expr :=
  InferType.mkForallParams params type |>.run {}

def mkAuxFunDecl (params : Array Param) (code : Code) (prefixName := `_f) : CompilerM FunDecl := do
  let type ← mkForallParams params (← code.inferType)
  let binderName ← mkFreshBinderName prefixName
  mkFunDecl binderName type params code

def mkAuxJpDecl (params : Array Param) (code : Code) (prefixName := `_jp) : CompilerM FunDecl := do
  mkAuxFunDecl params code prefixName

def mkAuxJpDecl' (fvarId : FVarId) (code : Code) (prefixName := `_jp) : CompilerM FunDecl := do
  let y ← mkFreshBinderName `_y
  let yType ← inferType (.fvar fvarId)
  let params := #[{ fvarId, binderName := y, type := yType }]
  mkAuxFunDecl params code prefixName

end Lean.Compiler.LCNF
