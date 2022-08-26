/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.LCNF.InferType

namespace Lean.Compiler.LCNF

namespace Check
open InferType

structure Context where
  /-- Join points that are in scope. -/
  jps : FVarIdSet := {}
  /-- Variables and local functions in scope -/
  vars : FVarIdSet := {}

structure State where
  /-- All free variables found -/
  all : FVarIdHashSet := {}

abbrev CheckM := ReaderT Context $ StateRefT State InferTypeM

def checkFVar (fvarId : FVarId) : CheckM Unit :=
  unless (← read).vars.contains fvarId do
    let localDecl ← getLocalDecl fvarId
    throwError "invalid out of scope free variable {localDecl.userName}"

def checkAppArgs (f : Expr) (args : Array Expr) : CheckM Unit := do
  let mut fType ← inferType f
  let mut j := 0
  for i in [:args.size] do
    let arg := args[i]!
    if fType.isAnyType then
      return ()
    fType := fType.headBeta
    let (d, b) ←
      match fType with
      | .forallE _ d b _ => pure (d, b)
      | _ =>
        fType := fType.instantiateRevRange j i args |>.headBeta
        match fType with
        | .forallE _ d b _ => j := i; pure (d, b)
        | _ =>
          if fType.isAnyType then return ()
          throwError "function expected at{indentExpr (mkAppN f args)}\narrow type expected{indentExpr fType}"
    let argType ← inferType arg
    let expectedType := d.instantiateRevRange j i args
    unless compatibleTypes argType expectedType do
      throwError "type mismatch at LCNF application{indentExpr (mkAppN f args)}\nargument {arg} has type{indentExpr argType}\nbut is expected to have type{indentExpr expectedType}"
    unless isTypeFormerType expectedType || expectedType.erased do
      unless arg.isFVar do
        throwError "invalid LCNF application{indentExpr (mkAppN f args)}\nargument{indentExpr arg}\nmust be a free variable"
      checkFVar arg.fvarId!
    fType := b

def checkApp (f : Expr) (args : Array Expr) : CheckM Unit := do
  unless f.isConst || f.isFVar do
    throwError "unexpected function application, function must be a constant or free variable{indentExpr (mkAppN f args)}"
  if f.isFVar then
    checkFVar f.fvarId!
  checkAppArgs f args

def checkExpr (e : Expr) : CheckM Unit :=
  match e with
  | .lit _ => pure ()
  | .app .. => checkApp e.getAppFn e.getAppArgs
  | .proj _ _ (.fvar fvarId) => checkFVar fvarId
  | .mdata _ (.fvar fvarId)  => checkFVar fvarId
  | .const _ _ => pure () -- TODO: check number of universe level parameters
  | .fvar fvarId => checkFVar fvarId
  | _ => throwError "unexpected expression at LCNF{indentExpr e}"

def checkJpInScope (jp : FVarId) : CheckM Unit := do
  unless (← read).jps.contains jp do
    /-
    We cannot jump to join points defined out of the scope of a local function declaration.
    For example, the following is an invalid LCNF.
    ```
    jp_1 := fun x => ... -- Some join point
    let f := fun y => -- Local function declaration.
      ...
      jp_1 _x.n -- jump to a join point that is not in the scope of `f`.
    ```
    -/
    throwError "invalid jump to out of scope join point"

def checkLetDecl (letDecl : LetDecl) : CheckM Unit := do
  checkExpr letDecl.value
  let valueType ← inferType letDecl.value
  unless compatibleTypes letDecl.type valueType do
    throwError "type mismatch at `{letDecl.binderName}`, value has type{indentExpr valueType}\nbut is expected to have type{indentExpr letDecl.type}"

def addFVarId (fvarId : FVarId) : CheckM Unit := do
  if (← get).all.contains fvarId then
    throwError "invalid LCNF, free variables are not unique `{fvarId.name}`"
  modify fun s => { s with all := s.all.insert fvarId }

@[inline] def withFVarId (fvarId : FVarId) (x : CheckM α) : CheckM α := do
  addFVarId fvarId
  withReader (fun ctx => { ctx with vars := ctx.vars.insert fvarId }) x

@[inline] def withJp (fvarId : FVarId) (x : CheckM α) : CheckM α := do
  addFVarId fvarId
  withReader (fun ctx => { ctx with jps := ctx.jps.insert fvarId }) x

@[inline] def withParams (params : Array Param) (x : CheckM α) : CheckM α := do
  params.forM (addFVarId ·.fvarId)
  withReader (fun ctx => { ctx with vars := params.foldl (init := ctx.vars) fun vars p => vars.insert p.fvarId })
    x

mutual

partial def checkFunDeclCore (declName : Name) (type : Expr) (params : Array Param) (value : Code) : CheckM Unit := do
  let valueType ← withParams params do
    mkForallParams params (← check value)
  unless compatibleTypes type valueType do
    throwError "type mismatch at `{declName}`, value has type{indentExpr valueType}\nbut is expected to have type{indentExpr type}"

partial def checkFunDecl (funDecl : FunDecl) : CheckM Unit :=
  checkFunDeclCore funDecl.binderName funDecl.type funDecl.params funDecl.value

partial def checkCases (c : Cases) : CheckM Expr := do
  let mut ctorNames : NameSet := {}
  let mut hasDefault := false
  checkFVar c.discr
  let discrType ← inferFVarType c.discr
  let .const declName _ := discrType.headBeta.getAppFn | throwError "unexpected LCNF discriminant type {discrType}"
  unless c.typeName == declName do
    throwError "invalid LCNF `{c.typeName}.casesOn`, discriminant has type{indentExpr discrType}"
  for alt in c.alts do
    let type ←
      match alt with
      | .default k => hasDefault := true; check k
      | .alt ctorName params k =>
        if ctorNames.contains ctorName then
          throwError "invalid LCNF `cases`, alternative `{ctorName}` occurs more than once"
        ctorNames := ctorNames.insert ctorName
        let .ctorInfo val ← getConstInfo ctorName | throwError "invalid LCNF `cases`, `{ctorName}` is not a constructor name"
        unless val.induct == c.typeName do
          throwError "invalid LCNF `cases`, `{ctorName}` is not a constructor of `{c.typeName}`"
        unless params.size == val.numFields do
          throwError "invalid LCNF `cases`, `{ctorName}` has # {val.numFields} fields, but alternative has # {params.size} alternatives"
        -- TODO: check whether the ctor field types as parameter types match.
        withParams params do check k
    unless compatibleTypes type c.resultType do
      throwError "type mismatch at LCNF `cases` alternative\nhas type{indentExpr type}\nbut is expected to have type{indentExpr c.resultType}"
  return c.resultType

partial def check (code : Code) : CheckM Expr := do
  match code with
  | .let decl k => checkLetDecl decl; withFVarId decl.fvarId do check k
  | .fun decl k =>
    -- Remark: local function declarations should not jump to out of scope join points
    withReader (fun ctx => { ctx with jps := {} }) do checkFunDecl decl
    withFVarId decl.fvarId do check k
  | .jp decl k => checkFunDecl decl; withJp decl.fvarId do check k
  | .cases c => checkCases c
  | .jmp fvarId args =>
    checkJpInScope fvarId
    let decl ← getFunDecl fvarId
    unless decl.getArity == args.size do
      throwError "invalid LCNF `jmp`, join point has #{decl.getArity} parameters, but #{args.size} were provided"
    checkAppArgs (.fvar fvarId) args; code.inferType
  | .return fvarId => checkFVar fvarId; code.inferType
  | .unreach .. => code.inferType

end

def run (x : CheckM α) : CompilerM α :=
  x |>.run {} |>.run' {} |>.run {}

end Check

def Decl.check (decl : Decl) : CompilerM Unit := do
  Check.run do Check.checkFunDeclCore decl.name decl.type decl.params decl.value

end Lean.Compiler.LCNF
