/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.CoreM
import Lean.Compiler.LCNF.Basic
import Lean.Compiler.LCNF.LCtx
import Lean.Compiler.LCNF.ConfigOptions

namespace Lean.Compiler.LCNF
/--
The pipeline phase a certain `Pass` is supposed to happen in.
-/
inductive Phase where
  /-- Here we still carry most of the original type information, most
  of the dependent portion is already (partially) erased though. -/
  | base
  /-- In this phase polymorphism has been eliminated. -/
  | mono
  /-- In this phase impure stuff such as RC or efficient BaseIO transformations happen. -/
  | impure
  deriving Inhabited

/--
The state managed by the `CompilerM` `Monad`.
-/
structure CompilerM.State where
  /--
  A `LocalContext` to store local declarations from let binders
  and other constructs in as we move through `Expr`s.
  -/
  lctx     : LCtx := {}
  /-- Next auxiliary variable suffix -/
  nextIdx : Nat := 1
  deriving Inhabited

structure CompilerM.Context where
  phase : Phase
  config : ConfigOptions
  deriving Inhabited

abbrev CompilerM := ReaderT CompilerM.Context $ StateRefT CompilerM.State CoreM

@[inline] def withPhase (phase : Phase) (x : CompilerM α) : CompilerM α :=
  withReader (fun ctx => { ctx with phase }) x

def getPhase : CompilerM Phase :=
  return (← read).phase

instance : AddMessageContext CompilerM where
  addMessageContext msgData := do
    let env ← getEnv
    let lctx := (← get).lctx.toLocalContext
    let opts ← getOptions
    return MessageData.withContext { env, lctx, opts, mctx := {} } msgData

def getType (fvarId : FVarId) : CompilerM Expr := do
  let lctx := (← get).lctx
  if let some decl := lctx.letDecls.find? fvarId then
    return decl.type
  else if let some decl := lctx.params.find? fvarId then
    return decl.type
  else if let some decl := lctx.funDecls.find? fvarId then
    return decl.type
  else
    throwError "unknown free variable {fvarId.name}"

def getBinderName (fvarId : FVarId) : CompilerM Name := do
  let lctx := (← get).lctx
  if let some decl := lctx.letDecls.find? fvarId then
    return decl.binderName
  else if let some decl := lctx.params.find? fvarId then
    return decl.binderName
  else if let some decl := lctx.funDecls.find? fvarId then
    return decl.binderName
  else
    throwError "unknown free variable {fvarId.name}"

def findParam? (fvarId : FVarId) : CompilerM (Option Param) :=
  return (← get).lctx.params.find? fvarId

def findLetDecl? (fvarId : FVarId) : CompilerM (Option LetDecl) :=
  return (← get).lctx.letDecls.find? fvarId

def findFunDecl? (fvarId : FVarId) : CompilerM (Option FunDecl) :=
  return (← get).lctx.funDecls.find? fvarId

def getParam (fvarId : FVarId) : CompilerM Param := do
  let some param ← findParam? fvarId | throwError "unknown parameter {fvarId.name}"
  return param

def getLetDecl (fvarId : FVarId) : CompilerM LetDecl := do
  let some decl ← findLetDecl? fvarId | throwError "unknown let-declaration {fvarId.name}"
  return decl

def getFunDecl (fvarId : FVarId) : CompilerM FunDecl := do
  let some decl ← findFunDecl? fvarId | throwError "unknown local function {fvarId.name}"
  return decl

@[inline] def modifyLCtx (f : LCtx → LCtx) : CompilerM Unit := do
   modify fun s => { s with lctx := f s.lctx }

def eraseLetDecl (decl : LetDecl) : CompilerM Unit := do
  modifyLCtx fun lctx => lctx.eraseLetDecl decl

def eraseFunDecl (decl : FunDecl) (recursive := true) : CompilerM Unit := do
  modifyLCtx fun lctx => lctx.eraseFunDecl decl recursive

def eraseCode (code : Code) : CompilerM Unit := do
  modifyLCtx fun lctx => lctx.eraseCode code

def eraseParam (param : Param) : CompilerM Unit :=
  modifyLCtx fun lctx => lctx.eraseParam param

def eraseParams (params : Array Param) : CompilerM Unit :=
  modifyLCtx fun lctx => lctx.eraseParams params

def eraseCodeDecl (decl : CodeDecl) : CompilerM Unit := do
  match decl with
  | .let decl => eraseLetDecl decl
  | .jp decl | .fun decl => eraseFunDecl decl

/--
Erase all free variables occurring in `decls` from the local context.
-/
def eraseCodeDecls (decls : Array CodeDecl) : CompilerM Unit := do
  decls.forM fun decl => eraseCodeDecl decl

def eraseDecl (decl : Decl) : CompilerM Unit := do
  eraseParams decl.params
  eraseCode decl.value

/--
A free variable substitution.
We use these substitutions when inlining definitions and "internalizing" LCNF code into `CompilerM`.
During the internalization process, we ensure all free variables in the LCNF code do not collide with existing ones
at the `CompilerM` local context.
Remark: in LCNF, (computationally relevant) data is in A-normal form, but this is not the case for types and type formers.
So, when inlining we often want to replace a free variable with a type or type former.

The substitution contains entries `fvarId ↦ e` s.t., `e` is a valid LCNF argument. That is,
it is a free variable, a type (or type former), or `lcErased`.

`Check.lean` contains a substitution validator.
-/
abbrev FVarSubst := HashMap FVarId Expr

/--
Replace the free variables in `e` using the given substitution.

If `translator = true`, then we assume the free variables occurring in the range of the substitution are in another
local context. For example, `translator = true` during internalization where we are making sure all free variables
in a given expression are replaced with new ones that do not collide with the ones in the current local context.

If `translator = false`, we assume the substitution contains free variable replacements in the same local context,
and given entries such as `x₁ ↦ x₂`, `x₂ ↦ x₃`, ..., `xₙ₋₁ ↦ xₙ`, and the expression `f x₁ x₂`, we want the resulting
expression to be `f xₙ xₙ`. We use this setting, for example, in the simplifier.
-/
private partial def normExprImp (s : FVarSubst) (e : Expr) (translator : Bool) : Expr :=
  go e
where
  goApp (e : Expr) : Expr :=
    match e with
    | .app f a => e.updateApp! (goApp f) (go a)
    | _ => go e

  go (e : Expr) : Expr :=
    if e.hasFVar then
      match e with
      | .fvar fvarId => match s.find? fvarId with
        | some e => if translator then e else go e
        | none => e
      | .lit .. | .const .. | .sort .. | .mvar .. | .bvar .. => e
      | .app f a => e.updateApp! (goApp f) (go a) |>.headBeta
      | .mdata _ b => e.updateMData! (go b)
      | .proj _ _ b => e.updateProj! (go b)
      | .forallE _ d b _ => e.updateForallE! (go d) (go b)
      | .lam _ d b _ => e.updateLambdaE! (go d) (go b)
      | .letE .. => unreachable! -- Valid LCNF does not contain `let`-declarations
    else
      e

/--
Normalize the given free variable.
See `normExprImp` for documentation on the `translator` parameter.
This function is meant to be used in contexts where the input free-variable is computationally relevant.
This function panics if the substitution is mapping `fvarId` to an expression that is not another free variable.
That is, it is not a type (or type former), nor `lcErased`. Recall that a valid `FVarSubst` contains only
expressions that are free variables, `lcErased`, or type formers.
-/
private partial def normFVarImp (s : FVarSubst) (fvarId : FVarId) (translator : Bool) : FVarId :=
  match s.find? fvarId with
  | some (.fvar fvarId') =>
    if translator then
      fvarId'
    else
      normFVarImp s fvarId' translator
  | some e => panic! s!"invalid LCNF substitution of free variable with expression {e}"
  | none => fvarId

/--
Interface for monads that have a free substitutions.
-/
class MonadFVarSubst (m : Type → Type) (translator : outParam Bool) where
  getSubst : m FVarSubst

export MonadFVarSubst (getSubst)

instance (m n) [MonadLift m n] [MonadFVarSubst m t] : MonadFVarSubst n t where
  getSubst := liftM (getSubst : m _)

class MonadFVarSubstState (m : Type → Type) where
  modifySubst : (FVarSubst → FVarSubst) → m Unit

export MonadFVarSubstState (modifySubst)

instance (m n) [MonadLift m n] [MonadFVarSubstState m] : MonadFVarSubstState n where
  modifySubst f := liftM (modifySubst f : m _)

/--
Add the entry `fvarId ↦ fvarId'` to the free variable substitution.
-/
@[inline] def addFVarSubst [MonadFVarSubstState m] (fvarId : FVarId) (fvarId' : FVarId) : m Unit :=
  modifySubst fun s => s.insert fvarId (.fvar fvarId')

/--
Add the substitution `fvarId ↦ e`, `e` must be a valid LCNF argument.
That is, it must be a free variable, type (or type former), or `lcErased`.

See `Check.lean` for the free variable substitution checker.
-/
@[inline] def addSubst [MonadFVarSubstState m] (fvarId : FVarId) (e : Expr) : m Unit :=
  modifySubst fun s => s.insert fvarId e

@[inline, inheritDoc normFVarImp] def normFVar [MonadFVarSubst m t] [Monad m] (fvarId : FVarId) : m FVarId :=
  return normFVarImp (← getSubst) fvarId t

@[inline, inheritDoc normExprImp] def normExpr [MonadFVarSubst m t] [Monad m] (e : Expr) : m Expr :=
  return normExprImp (← getSubst) e t

/--
Normalize the given expressions using the current substitution.
-/
def normExprs [MonadFVarSubst m t] [Monad m] (es : Array Expr) : m (Array Expr) :=
  es.mapMonoM normExpr

def mkFreshBinderName (binderName := `_x): CompilerM Name := do
  let declName := .num binderName (← get).nextIdx
  modify fun s => { s with nextIdx := s.nextIdx + 1 }
  return declName

/-!
Helper functions for creating LCNF local declarations.
-/

def mkParam (binderName : Name) (type : Expr) (borrow : Bool) : CompilerM Param := do
  let fvarId ← mkFreshFVarId
  let param := { fvarId, binderName, type, borrow }
  modifyLCtx fun lctx => lctx.addParam param
  return param

def mkLetDecl (binderName : Name) (type : Expr) (value : Expr) : CompilerM LetDecl := do
  let fvarId ← mkFreshFVarId
  let decl := { fvarId, binderName, type, value }
  modifyLCtx fun lctx => lctx.addLetDecl decl
  return decl

def mkFunDecl (binderName : Name) (type : Expr) (params : Array Param) (value : Code) : CompilerM FunDecl := do
  let fvarId ← mkFreshFVarId
  let funDecl := { fvarId, binderName, type, params, value }
  modifyLCtx fun lctx => lctx.addFunDecl funDecl
  return funDecl

private unsafe def updateParamImp (p : Param) (type : Expr) : CompilerM Param := do
  if ptrEq type p.type then
    return p
  else
    let p := { p with type }
    modifyLCtx fun lctx => lctx.addParam p
    return p

@[implementedBy updateParamImp] opaque Param.update (p : Param) (type : Expr) : CompilerM Param

private unsafe def updateLetDeclImp (decl : LetDecl) (type : Expr) (value : Expr) : CompilerM LetDecl := do
  if ptrEq type decl.type && ptrEq value decl.value then
    return decl
  else
    let decl := { decl with type, value }
    modifyLCtx fun lctx => lctx.addLetDecl decl
    return decl

@[implementedBy updateLetDeclImp] opaque LetDecl.update (decl : LetDecl) (type : Expr) (value : Expr) : CompilerM LetDecl

def LetDecl.updateValue (decl : LetDecl) (value : Expr) : CompilerM LetDecl :=
  decl.update decl.type value

private unsafe def updateFunDeclImp (decl: FunDecl) (type : Expr) (params : Array Param) (value : Code) : CompilerM FunDecl := do
  if ptrEq type decl.type && ptrEq params decl.params && ptrEq value decl.value then
    return decl
  else
    let decl := { decl with type, params, value }
    modifyLCtx fun lctx => lctx.addFunDecl decl
    return decl

@[implementedBy updateFunDeclImp] opaque FunDeclCore.update (decl: FunDecl) (type : Expr) (params : Array Param) (value : Code) : CompilerM FunDecl

abbrev FunDeclCore.update' (decl : FunDecl) (type : Expr) (value : Code) : CompilerM FunDecl :=
  decl.update type decl.params value

abbrev FunDeclCore.updateValue (decl : FunDecl) (value : Code) : CompilerM FunDecl :=
  decl.update decl.type decl.params value

@[inline] def normParam [MonadLiftT CompilerM m] [Monad m] [MonadFVarSubst m t] (p : Param) : m Param := do
  p.update (← normExpr p.type)

def normParams [MonadLiftT CompilerM m] [Monad m] [MonadFVarSubst m t] (ps : Array Param) : m (Array Param) :=
  ps.mapMonoM normParam

def normLetDecl [MonadLiftT CompilerM m] [Monad m] [MonadFVarSubst m t] (decl : LetDecl) : m LetDecl := do
  decl.update (← normExpr decl.type) (← normExpr decl.value)

abbrev NormalizerM (_translator : Bool) := ReaderT FVarSubst CompilerM

instance : MonadFVarSubst (NormalizerM t) t where
  getSubst := read

mutual
  partial def normFunDeclImp (decl : FunDecl) : NormalizerM t FunDecl  := do
    let type ← normExpr decl.type
    let params ← normParams decl.params
    let value ← normCodeImp decl.value
    decl.update type params value

  partial def normCodeImp (code : Code) : NormalizerM t Code := do
    match code with
    | .let decl k => return code.updateLet! (← normLetDecl decl) (← normCodeImp k)
    | .fun decl k | .jp decl k => return code.updateFun! (← normFunDeclImp decl) (← normCodeImp k)
    | .return fvarId => return code.updateReturn! (← normFVar fvarId)
    | .jmp fvarId args => return code.updateJmp! (← normFVar fvarId) (← normExprs args)
    | .unreach type => return code.updateUnreach! (← normExpr type)
    | .cases c =>
      let resultType ← normExpr c.resultType
      let discr ← normFVar c.discr
      let alts ← c.alts.mapMonoM fun alt =>
        match alt with
        | .alt _ params k => return alt.updateAlt! (← normParams params) (← normCodeImp k)
        | .default k => return alt.updateCode (← normCodeImp k)
      return code.updateCases! resultType discr alts
end

@[inline] def normFunDecl [MonadLiftT CompilerM m] [Monad m] [MonadFVarSubst m t] (decl : FunDecl) : m FunDecl := do
  normFunDeclImp (t := t) decl (← getSubst)

/-- Similar to `internalize`, but does not refresh `FVarId`s. -/
@[inline] def normCode [MonadLiftT CompilerM m] [Monad m] [MonadFVarSubst m t] (code : Code) : m Code := do
  normCodeImp (t := t) code (← getSubst)

def replaceExprFVars (e : Expr) (s : FVarSubst) (translator : Bool) : CompilerM Expr :=
  (normExpr e : NormalizerM translator Expr).run s

def replaceFVars (code : Code) (s : FVarSubst) (translator : Bool) : CompilerM Code :=
  (normCode code : NormalizerM translator Code).run s

def mkFreshJpName : CompilerM Name := do
  mkFreshBinderName `_jp

def mkAuxParam (type : Expr) (borrow := false) : CompilerM Param := do
  mkParam (← mkFreshBinderName `_y) type borrow

def getConfig : CompilerM ConfigOptions :=
  return (← read).config

def CompilerM.run (x : CompilerM α) (s : State := {}) (phase : Phase := .base) : CoreM α := do
  x { phase, config := toConfigOptions (← getOptions) } |>.run' s

end Lean.Compiler.LCNF
