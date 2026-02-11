/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Compiler.LCNF.LCtx
public import Lean.Compiler.LCNF.ConfigOptions

public section

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
  | impure
  deriving Inhabited, DecidableEq

@[expose, reducible] def Phase.toPurity : Phase → Purity
  | .base | .mono => .pure
  | .impure => .impure

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

@[always_inline]
instance : Monad CompilerM := let i := inferInstanceAs (Monad CompilerM); { pure := i.pure, bind := i.bind }

@[inline] def withPhase (phase : Phase) (x : CompilerM α) : CompilerM α :=
  withReader (fun ctx => { ctx with phase }) x

def getPhase : CompilerM Phase :=
  return (← read).phase

def getPurity : CompilerM Purity :=
  return (← getPhase).toPurity

def inBasePhase : CompilerM Bool :=
  return (← getPhase) matches .base

instance : AddMessageContext CompilerM where
  addMessageContext msgData := do
    let env ← getEnv
    let lctx := (← get).lctx.toLocalContext (← getPurity)
    let opts ← getOptions
    return MessageData.withContext { env, lctx, opts, mctx := {} } msgData

def getType (fvarId : FVarId) : CompilerM Expr := do
  let lctx := (← get).lctx
  let pu ← getPurity
  if let some decl := (lctx.letDecls pu)[fvarId]? then
    return decl.type
  else if let some decl := (lctx.params pu)[fvarId]? then
    return decl.type
  else if let some decl := (lctx.funDecls pu)[fvarId]? then
    return decl.type
  else
    throwError "unknown free variable {fvarId.name}"

def getBinderName (fvarId : FVarId) : CompilerM Name := do
  let lctx := (← get).lctx
  let pu ← getPurity
  if let some decl := (lctx.letDecls pu)[fvarId]? then
    return decl.binderName
  else if let some decl := (lctx.params pu)[fvarId]? then
    return decl.binderName
  else if let some decl := (lctx.funDecls pu)[fvarId]? then
    return decl.binderName
  else
    throwError "unknown free variable {fvarId.name}"

def findParam? (fvarId : FVarId) : CompilerM (Option (Param pu)) := do
  return ((← get).lctx.params pu)[fvarId]?

def findLetDecl? (fvarId : FVarId) : CompilerM (Option (LetDecl pu)) := do
  return ((← get).lctx.letDecls pu)[fvarId]?

def findFunDecl? (fvarId : FVarId) : CompilerM (Option (FunDecl pu)) := do
  return ((← get).lctx.funDecls pu)[fvarId]?

def findLetValue? (fvarId : FVarId) : CompilerM (Option (LetValue pu)) := do
  let some { value, .. } ← findLetDecl? fvarId | return none
  return some value

def isConstructorApp (fvarId : FVarId) : CompilerM Bool := do
  let some (.const declName _ _) ← findLetValue? fvarId | return false
  return (← getEnv).find? declName matches some (.ctorInfo ..)

def Arg.isConstructorApp (arg : Arg pu) : CompilerM Bool := do
  let .fvar fvarId := arg | return false
  LCNF.isConstructorApp fvarId

def getParam (fvarId : FVarId) : CompilerM (Param pu) := do
  let some param ← findParam? fvarId | throwError "unknown parameter {fvarId.name}"
  return param

def getLetDecl (fvarId : FVarId) : CompilerM (LetDecl pu) := do
  let some decl ← findLetDecl? fvarId | throwError "unknown let-declaration {fvarId.name}"
  return decl

def getFunDecl (fvarId : FVarId) : CompilerM (FunDecl pu) := do
  let some decl ← findFunDecl? fvarId | throwError "unknown local function {fvarId.name}"
  return decl

@[inline] def modifyLCtx (f : LCtx → LCtx) : CompilerM Unit := do
   modify fun s => { s with lctx := f s.lctx }

def eraseLetDecl (decl : LetDecl pu) : CompilerM Unit := do
  modifyLCtx fun lctx => lctx.eraseLetDecl decl

def eraseFunDecl (decl : FunDecl pu) (recursive := true) : CompilerM Unit := do
  modifyLCtx fun lctx => lctx.eraseFunDecl decl recursive

def eraseCode (code : Code pu) : CompilerM Unit := do
  modifyLCtx fun lctx => lctx.eraseCode code

def eraseParam (param : Param pu) : CompilerM Unit :=
  modifyLCtx fun lctx => lctx.eraseParam param

def eraseParams (params : Array (Param pu)) : CompilerM Unit :=
  modifyLCtx fun lctx => lctx.eraseParams params

def eraseCodeDecl (decl : CodeDecl pu) : CompilerM Unit := do
  match decl with
  | .let decl => eraseLetDecl decl
  | .jp decl | .fun decl _ => eraseFunDecl decl
  | .sset .. | .uset .. => return ()

/--
Erase all free variables occurring in `decls` from the local context.
-/
def eraseCodeDecls (decls : Array (CodeDecl pu)) : CompilerM Unit := do
  decls.forM fun decl => eraseCodeDecl decl

def eraseDecl (decl : Decl pu) : CompilerM Unit := do
  eraseParams decl.params
  decl.value.forCodeM eraseCode

abbrev Decl.erase (decl : Decl pu) : CompilerM Unit :=
  eraseDecl decl

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
abbrev FVarSubst (pu : Purity) := Std.HashMap FVarId (Arg pu)

/--
Replace the free variables in `e` using the given substitution.

If `translator = true`, then we assume the free variables occurring in the range of the substitution are in another
local context. For example, `translator = true` during internalization where we are making sure all free variables
in a given expression are replaced with new ones that do not collide with the ones in the current local context.

If `translator = false`, we assume the substitution contains free variable replacements in the same local context,
and given entries such as `x₁ ↦ x₂`, `x₂ ↦ x₃`, ..., `xₙ₋₁ ↦ xₙ`, and the expression `f x₁ x₂`, we want the resulting
expression to be `f xₙ xₙ`. We use this setting, for example, in the simplifier.
-/
private partial def normExprImp (s : FVarSubst pu) (e : Expr) (translator : Bool) : Expr :=
  go e
where
  goApp (e : Expr) : Expr :=
    match e with
    | .app f a => e.updateApp! (goApp f) (go a)
    | _ => go e

  go (e : Expr) : Expr :=
    if e.hasFVar then
      match e with
      | .fvar fvarId => match s[fvarId]? with
        | some (.fvar fvarId') => if translator then .fvar fvarId' else go (.fvar fvarId')
        | some (.type e _) => if translator then e else go e
        | some .erased => erasedExpr
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
Result type for `normFVar` and `normFVarImp`.
-/
inductive NormFVarResult where
  | /-- New free variable. -/
    fvar (fvarId : FVarId)
  | /--
    Free variable has been erased. This can happen when instantiating polymorphic code
    with computationally irrelevant stuff. -/
    erased
  deriving Inhabited

/--
Normalize the given free variable.
See `normExprImp` for documentation on the `translator` parameter.
This function is meant to be used in contexts where the input free-variable is computationally relevant.
This function panics if the substitution is mapping `fvarId` to an expression that is not another free variable.
That is, it is not a type (or type former), nor `lcErased`. Recall that a valid `FVarSubst` contains only
expressions that are free variables, `lcErased`, or type formers.
-/
partial def normFVarImp (s : FVarSubst pu) (fvarId : FVarId) (translator : Bool) : NormFVarResult :=
  match s[fvarId]? with
  | some (.fvar fvarId') =>
    if translator then
      .fvar fvarId'
    else
      normFVarImp s fvarId' translator
  -- Types and type formers are only preserved as hints and
  -- are erased in computationally relevant contexts.
  | some .erased | some (.type _ _) => .erased
  | none => .fvar fvarId

/--
Replace the free variables in `arg` using the given substitution.

See `normExprImp`
-/
private partial def normArgImp (s : FVarSubst pu) (arg : Arg pu) (translator : Bool) : Arg pu :=
  match arg with
  | .erased => arg
  | .fvar fvarId =>
    match s[fvarId]? with
    | some (arg'@(.fvar _)) =>
      if translator then arg' else normArgImp s arg' translator
    | some (arg'@.erased) | some (arg'@(.type _ _)) => arg'
    | none => arg
  | .type e _ => arg.updateType! (normExprImp s e translator)

private def normArgsImp (s : FVarSubst pu) (args : Array (Arg pu)) (translator : Bool) : Array (Arg pu) :=
  args.mapMono (normArgImp s · translator)

/--
Replace the free variables in `e` using the given substitution.

See `normExprImp`
-/
private partial def normLetValueImp (s : FVarSubst pu) (e : LetValue pu) (translator : Bool) : LetValue pu :=
  match e with
  | .erased | .lit .. => e
  | .proj _ _ fvarId _ | .sproj _ _ fvarId _ | .uproj _ fvarId _ | .oproj _ fvarId _  =>
    match normFVarImp s fvarId translator with
    | .fvar fvarId' => e.updateProj! fvarId'
    | .erased => .erased
  | .const _ _ args _ | .ctor _ args _ | .fap _ args _ | .pap _ args _ =>
    e.updateArgs! (normArgsImp s args translator)
  | .fvar fvarId args => match normFVarImp s fvarId translator with
    | .fvar fvarId' => e.updateFVar! fvarId' (normArgsImp s args translator)
    | .erased => .erased
  | .reset n fvarId _ =>
    match normFVarImp s fvarId translator with
    | .fvar fvarId' => e.updateReset! n fvarId'
    | .erased => .erased
  | .reuse fvarId info updateHeader args _ =>
    match normFVarImp s fvarId translator with
    | .fvar fvarId' => e.updateReuse! fvarId' info updateHeader (normArgsImp s args translator)
    | .erased => .erased

/--
Interface for monads that have a free substitutions.
-/
class MonadFVarSubst (m : Type → Type) (pu : outParam Purity) (translator : outParam Bool) where
  getSubst : m (FVarSubst pu)

export MonadFVarSubst (getSubst)

instance (m n) [MonadLift m n] [MonadFVarSubst m pu t] : MonadFVarSubst n pu t where
  getSubst := liftM (getSubst : m _)

class MonadFVarSubstState (m : Type → Type) (pu : outParam Purity) where
  modifySubst : (FVarSubst pu → FVarSubst pu) → m Unit

export MonadFVarSubstState (modifySubst)

instance (m n) [MonadLift m n] [MonadFVarSubstState m pu] : MonadFVarSubstState n pu where
  modifySubst f := liftM (modifySubst f : m _)

/--
Add the substitution `fvarId ↦ e`, `e` must be a valid LCNF `Arg`.

See `Check.lean` for the free variable substitution checker.
-/
@[inline] def addSubst [MonadFVarSubstState m pu] (fvarId : FVarId) (arg : Arg pu) : m Unit :=
  modifySubst fun s => s.insert fvarId arg

/--
Add the entry `fvarId ↦ fvarId'` to the free variable substitution.
-/
@[inline] def addFVarSubst [MonadFVarSubstState m ph] (fvarId : FVarId) (fvarId' : FVarId) : m Unit :=
  modifySubst fun s => s.insert fvarId (.fvar fvarId')

@[inline, inherit_doc normFVarImp] def normFVar [MonadFVarSubst m pu t] [Monad m] (fvarId : FVarId) : m NormFVarResult :=
  return normFVarImp (← getSubst) fvarId t

@[inline, inherit_doc normExprImp] def normExpr [MonadFVarSubst m pu t] [Monad m] (e : Expr) : m Expr :=
  return normExprImp (← getSubst) e t

@[inline, inherit_doc normArgImp] def normArg [MonadFVarSubst m pu t] [Monad m] (arg : Arg pu) : m (Arg pu) :=
  return normArgImp (← getSubst) arg t

@[inline, inherit_doc normLetValueImp] def normLetValue [MonadFVarSubst m pu t] [Monad m] (e : LetValue pu) : m (LetValue pu) :=
  return normLetValueImp (← getSubst) e t

@[inherit_doc normExprImp, inline]
def normExprCore (s : FVarSubst pu) (e : Expr) (translator : Bool) : Expr :=
  normExprImp s e translator

/--
Normalize the given arguments using the current substitution.
-/
def normArgs [MonadFVarSubst m pu t] [Monad m] (args : Array (Arg pu)) : m (Array (Arg pu)) :=
  return normArgsImp (← getSubst) args t

def mkFreshBinderName (binderName := `_x): CompilerM Name := do
  let declName := .num binderName (← get).nextIdx
  modify fun s => { s with nextIdx := s.nextIdx + 1 }
  return declName

def ensureNotAnonymous (binderName : Name) (baseName : Name) : CompilerM Name :=
  if binderName.isAnonymous then
    mkFreshBinderName baseName
  else
    return binderName

/-!
Helper functions for creating LCNF local declarations.
-/

def mkParam (binderName : Name) (type : Expr) (borrow : Bool) : CompilerM (Param pu) := do
  let fvarId ← mkFreshFVarId
  let binderName ← ensureNotAnonymous binderName `_y
  let param := { fvarId, binderName, type, borrow }
  modifyLCtx fun lctx => lctx.addParam param
  return param

def mkLetDecl (binderName : Name) (type : Expr) (value : LetValue pu) : CompilerM (LetDecl pu) := do
  let fvarId ← mkFreshFVarId
  let binderName ← ensureNotAnonymous binderName `_x
  let decl := { fvarId, binderName, type, value }
  modifyLCtx fun lctx => lctx.addLetDecl decl
  return decl

def mkFunDecl (binderName : Name) (type : Expr) (params : Array (Param pu)) (value : Code pu) : CompilerM (FunDecl pu) := do
  let fvarId ← mkFreshFVarId
  let binderName ← ensureNotAnonymous binderName `_f
  let funDecl := ⟨fvarId, binderName, params, type, value⟩
  modifyLCtx fun lctx => lctx.addFunDecl funDecl
  return funDecl

def mkLetDeclErased : CompilerM (LetDecl pu) := do
  mkLetDecl (← mkFreshBinderName `_x) erasedExpr .erased

def mkReturnErased : CompilerM (Code pu) := do
  let auxDecl ← mkLetDeclErased
  return .let auxDecl (.return auxDecl.fvarId)

private unsafe def updateParamImp (p : Param pu) (type : Expr) : CompilerM (Param pu) := do
  if ptrEq type p.type then
    return p
  else
    let p := { p with type }
    modifyLCtx fun lctx => lctx.addParam p
    return p

@[implemented_by updateParamImp] opaque Param.update (p : Param pu) (type : Expr) : CompilerM (Param pu)

private unsafe def updateParamBorrowImp (p : Param pu) (borrow : Bool) : CompilerM (Param pu) := do
  if borrow = p.borrow then
    return p
  else
    let p := { p with borrow }
    modifyLCtx fun lctx => lctx.addParam p
    return p

@[implemented_by updateParamBorrowImp] opaque Param.updateBorrow (p : Param pu) (borrow : Bool) : CompilerM (Param pu)

private unsafe def updateLetDeclImp (decl : LetDecl pu) (type : Expr) (value : LetValue pu) : CompilerM (LetDecl pu) := do
  if ptrEq type decl.type && ptrEq value decl.value then
    return decl
  else
    let decl := { decl with type, value }
    modifyLCtx fun lctx => lctx.addLetDecl decl
    return decl

@[implemented_by updateLetDeclImp] opaque LetDecl.update (decl : LetDecl pu) (type : Expr) (value : LetValue pu) : CompilerM (LetDecl pu)

def LetDecl.updateValue (decl : LetDecl pu) (value : LetValue pu) : CompilerM (LetDecl pu) :=
  decl.update decl.type value

private unsafe def updateFunDeclImp (decl : FunDecl pu) (type : Expr) (params : Array (Param pu)) (value : Code pu) : CompilerM (FunDecl pu) := do
  if ptrEq type decl.type && ptrEq params decl.params && ptrEq value decl.value then
    return decl
  else
    let decl := ⟨decl.fvarId, decl.binderName, params, type, value⟩
    modifyLCtx fun lctx => lctx.addFunDecl decl
    return decl

@[implemented_by updateFunDeclImp] opaque FunDecl.update (decl : FunDecl pu) (type : Expr) (params : Array (Param pu)) (value : Code pu) : CompilerM (FunDecl pu)

abbrev FunDecl.update' (decl : FunDecl pu) (type : Expr) (value : Code pu) : CompilerM (FunDecl pu) :=
  decl.update type decl.params value

abbrev FunDecl.updateValue (decl : FunDecl pu) (value : Code pu) : CompilerM (FunDecl pu) :=
  decl.update decl.type decl.params value

@[inline] def normParam [MonadLiftT CompilerM m] [Monad m] [MonadFVarSubst m pu t] (p : Param pu) : m (Param pu) := do
  p.update (← normExpr p.type)

def normParams [MonadLiftT CompilerM m] [Monad m] [MonadFVarSubst m pu t] (ps : Array (Param pu)) : m (Array (Param pu)) :=
  ps.mapMonoM normParam

def normLetDecl [MonadLiftT CompilerM m] [Monad m] [MonadFVarSubst m pu t] (decl : LetDecl pu) : m (LetDecl pu) := do
  decl.update (← normExpr decl.type) (← normLetValue decl.value)

abbrev NormalizerM (pu : Purity) (_translator : Bool) := ReaderT (FVarSubst pu) CompilerM

instance : MonadFVarSubst (NormalizerM pu t) pu t where
  getSubst := read

/--
If `result` is `.fvar fvarId`, then return `x fvarId`. Otherwise, it is `.erased`,
and method returns `let _x.i := .erased; return _x.i`.
-/
@[inline] def withNormFVarResult [MonadLiftT CompilerM m] [Monad m] (result : NormFVarResult) (x : FVarId → m (Code pu)) : m (Code pu) := do
  match result with
  | .fvar fvarId => x fvarId
  | .erased => mkReturnErased

mutual
  partial def normFunDeclImp (decl : FunDecl pu) : NormalizerM pu t (FunDecl pu) := do
    let type ← normExpr decl.type
    let params ← normParams decl.params
    let value ← normCodeImp decl.value
    decl.update type params value

  partial def normCodeImp (code : Code pu) : NormalizerM pu t (Code pu) := do
    match code with
    | .let decl k => return code.updateLet! (← normLetDecl decl) (← normCodeImp k)
    | .fun decl k _ | .jp decl k => return code.updateFun! (← normFunDeclImp decl) (← normCodeImp k)
    | .return fvarId => withNormFVarResult (← normFVar fvarId) fun fvarId => return code.updateReturn! fvarId
    | .jmp fvarId args => withNormFVarResult (← normFVar fvarId) fun fvarId => return code.updateJmp! fvarId (← normArgs args)
    | .unreach type => return code.updateUnreach! (← normExpr type)
    | .cases c =>
      let resultType ← normExpr c.resultType
      withNormFVarResult (← normFVar c.discr) fun discr => do
        let alts ← c.alts.mapMonoM fun alt =>
          match alt with
          | .alt _ params k _ => return alt.updateAlt! (← normParams params) (← normCodeImp k)
          | .default k | .ctorAlt _ k _ => return alt.updateCode (← normCodeImp k)
        return code.updateCases! resultType discr alts
    | .sset fvarId i offset y ty k _ =>
      withNormFVarResult (← normFVar fvarId) fun fvarId => do
      withNormFVarResult (← normFVar y) fun y => do
        return code.updateSset! fvarId i offset y (← normExpr ty) (← normCodeImp k)
    | .uset fvarId offset y k _ =>
      withNormFVarResult (← normFVar fvarId) fun fvarId => do
      withNormFVarResult (← normFVar y) fun y => do
        return code.updateUset! fvarId offset y (← normCodeImp k)
end

@[inline] def normFunDecl [MonadLiftT CompilerM m] [Monad m] [MonadFVarSubst m pu t] (decl : FunDecl pu) : m (FunDecl pu) := do
  normFunDeclImp (t := t) decl (← getSubst)

/-- Similar to `internalize`, but does not refresh `FVarId`s. -/
@[inline] def normCode [MonadLiftT CompilerM m] [Monad m] [MonadFVarSubst m pu t] (code : Code pu) : m (Code pu) := do
  normCodeImp (t := t) code (← getSubst)

def replaceExprFVars (e : Expr) (s : FVarSubst pu) (translator : Bool) : CompilerM Expr :=
  (normExpr e : NormalizerM pu translator Expr).run s

def replaceFVars (code : Code pu) (s : FVarSubst pu) (translator : Bool) : CompilerM (Code pu) :=
  (normCode code : NormalizerM pu translator (Code pu)).run s

def mkFreshJpName : CompilerM Name := do
  mkFreshBinderName `_jp

def mkAuxParam (type : Expr) (borrow := false) : CompilerM (Param pu) := do
  mkParam (← mkFreshBinderName `_y) type borrow

def getConfig : CompilerM ConfigOptions :=
  return (← read).config

def CompilerM.run (x : CompilerM α) (s : State := {}) (phase : Phase := .base) : CoreM α := do
  x { phase, config := toConfigOptions (← getOptions) } |>.run' s

/-- Environment extension for local caching of key-value pairs, not persisted in .olean files. -/
structure CacheExtension (α β : Type) [BEq α] [Hashable α] extends EnvExtension (List α × PHashMap α β)
deriving Inhabited

namespace CacheExtension

def register [BEq α] [Hashable α] [Inhabited β] :
    IO (CacheExtension α β) :=
  CacheExtension.mk <$> registerEnvExtension (pure ([], {})) (asyncMode := .sync)  -- compilation is non-parallel anyway
    (replay? := some fun oldState newState _ s =>
      let newEntries := newState.1.take (newState.1.length - oldState.1.length)
      newEntries.foldl (init := s) fun s e =>
        (e :: s.1, s.2.insert e (newState.2.find! e)))

def insert [BEq α] [Hashable α] [Inhabited β] (ext : CacheExtension α β) (a : α) (b : β) : CoreM Unit := do
  modifyEnv (ext.modifyState · fun ⟨as, m⟩ => (a :: as, m.insert a b))

def find? [BEq α] [Hashable α] [Inhabited β] (ext : CacheExtension α β) (a : α) : CoreM (Option β) := do
  return ext.toEnvExtension.getState (← getEnv) |>.2.find? a

end CacheExtension

end Lean.Compiler.LCNF
