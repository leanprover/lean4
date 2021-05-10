/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Data.LOption
import Lean.Environment
import Lean.Class
import Lean.ReducibilityAttrs
import Lean.Util.Trace
import Lean.Util.RecDepth
import Lean.Util.PPExt
import Lean.Util.OccursCheck
import Lean.Util.MonadBacktrack
import Lean.Compiler.InlineAttrs
import Lean.Meta.TransparencyMode
import Lean.Meta.DiscrTreeTypes
import Lean.Eval
import Lean.CoreM

/-
This module provides four (mutually dependent) goodies that are needed for building the elaborator and tactic frameworks.
1- Weak head normal form computation with support for metavariables and transparency modes.
2- Definitionally equality checking with support for metavariables (aka unification modulo definitional equality).
3- Type inference.
4- Type class resolution.

They are packed into the MetaM monad.
-/

namespace Lean.Meta

builtin_initialize isDefEqStuckExceptionId : InternalExceptionId ← registerInternalExceptionId `isDefEqStuck

structure Config where
  foApprox           : Bool := false
  ctxApprox          : Bool := false
  quasiPatternApprox : Bool := false
  /- When `constApprox` is set to true,
     we solve `?m t =?= c` using
     `?m := fun _ => c`
     when `?m t` is not a higher-order pattern and `c` is not an application as -/
  constApprox        : Bool := false
  /-
    When the following flag is set,
    `isDefEq` throws the exeption `Exeption.isDefEqStuck`
    whenever it encounters a constraint `?m ... =?= t` where
    `?m` is read only.
    This feature is useful for type class resolution where
    we may want to notify the caller that the TC problem may be solveable
    later after it assigns `?m`. -/
  isDefEqStuckEx     : Bool := false
  transparency       : TransparencyMode := TransparencyMode.default
  /- If zetaNonDep == false, then non dependent let-decls are not zeta expanded. -/
  zetaNonDep         : Bool := true
  /- When `trackZeta == true`, we store zetaFVarIds all free variables that have been zeta-expanded. -/
  trackZeta          : Bool := false
  unificationHints   : Bool := true

structure ParamInfo where
  implicit     : Bool      := false
  instImplicit : Bool      := false
  hasFwdDeps   : Bool      := false
  backDeps     : Array Nat := #[]
  deriving Inhabited

def ParamInfo.isExplicit (p : ParamInfo) : Bool :=
  !p.implicit && !p.instImplicit

structure FunInfo where
  paramInfo  : Array ParamInfo := #[]
  resultDeps : Array Nat       := #[]

structure InfoCacheKey where
  transparency : TransparencyMode
  expr         : Expr
  nargs?       : Option Nat
  deriving Inhabited, BEq

namespace InfoCacheKey
instance : Hashable InfoCacheKey :=
  ⟨fun ⟨transparency, expr, nargs⟩ => mixHash (hash transparency) <| mixHash (hash expr) (hash nargs)⟩
end InfoCacheKey

open Std (PersistentArray PersistentHashMap)

abbrev SynthInstanceCache := PersistentHashMap Expr (Option Expr)

abbrev InferTypeCache := PersistentExprStructMap Expr
abbrev FunInfoCache   := PersistentHashMap InfoCacheKey FunInfo
abbrev WhnfCache      := PersistentExprStructMap Expr
structure Cache where
  inferType     : InferTypeCache := {}
  funInfo       : FunInfoCache   := {}
  synthInstance : SynthInstanceCache := {}
  whnfDefault   : WhnfCache := {} -- cache for closed terms and `TransparencyMode.default`
  whnfAll       : WhnfCache := {} -- cache for closed terms and `TransparencyMode.all`
  deriving Inhabited

/--
 "Context" for a postponed universe constraint.
 `lhs` and `rhs` are the surrounding `isDefEq` call when the postponed constraint was created.
-/
structure DefEqContext where
  lhs            : Expr
  rhs            : Expr
  lctx           : LocalContext
  localInstances : LocalInstances

/--
  Auxiliary structure for representing postponed universe constraints.
  Remark: the fields `ref` and `rootDefEq?` are used for error message generation only.
  Remark: we may consider improving the error message generation in the future.
-/
structure PostponedEntry where
  ref  : Syntax -- We save the `ref` at entry creation time
  lhs  : Level
  rhs  : Level
  ctx? : Option DefEqContext -- Context for the surrounding `isDefEq` call when entry was created
  deriving Inhabited

structure State where
  mctx        : MetavarContext := {}
  cache       : Cache := {}
  /- When `trackZeta == true`, then any let-decl free variable that is zeta expansion performed by `MetaM` is stored in `zetaFVarIds`. -/
  zetaFVarIds : NameSet := {}
  postponed   : PersistentArray PostponedEntry := {}
  deriving Inhabited

structure SavedState where
  core        : Core.State
  meta        : State
  deriving Inhabited

structure Context where
  config         : Config               := {}
  lctx           : LocalContext         := {}
  localInstances : LocalInstances       := #[]
  /-- Not `none` when inside of an `isDefEq` test. See `PostponedEntry`. -/
  defEqCtx?      : Option DefEqContext  := none

abbrev MetaM  := ReaderT Context $ StateRefT State CoreM

instance : Inhabited (MetaM α) where
  default := fun _ _ => arbitrary

instance : MonadLCtx MetaM where
  getLCtx := return (← read).lctx

instance : MonadMCtx MetaM where
  getMCtx    := return (← get).mctx
  modifyMCtx f := modify fun s => { s with mctx := f s.mctx }

instance : AddMessageContext MetaM where
  addMessageContext := addMessageContextFull

protected def saveState : MetaM SavedState :=
  return { core := (← getThe Core.State), meta := (← get) }

/-- Restore backtrackable parts of the state. -/
def SavedState.restore (b : SavedState) : MetaM Unit := do
  Core.restore b.core
  modify fun s => { s with mctx := b.meta.mctx, zetaFVarIds := b.meta.zetaFVarIds, postponed := b.meta.postponed }

instance : MonadBacktrack SavedState MetaM where
  saveState      := Meta.saveState
  restoreState s := s.restore

@[inline] def MetaM.run (x : MetaM α) (ctx : Context := {}) (s : State := {}) : CoreM (α × State) :=
  x ctx |>.run s

@[inline] def MetaM.run' (x : MetaM α) (ctx : Context := {}) (s : State := {}) : CoreM α :=
  Prod.fst <$> x.run ctx s

@[inline] def MetaM.toIO (x : MetaM α) (ctxCore : Core.Context) (sCore : Core.State) (ctx : Context := {}) (s : State := {}) : IO (α × Core.State × State) := do
  let ((a, s), sCore) ← (x.run ctx s).toIO ctxCore sCore
  pure (a, sCore, s)

instance [MetaEval α] : MetaEval (MetaM α) :=
  ⟨fun env opts x _ => MetaEval.eval env opts x.run' true⟩

protected def throwIsDefEqStuck : MetaM α :=
  throw <| Exception.internal isDefEqStuckExceptionId

builtin_initialize
  registerTraceClass `Meta
  registerTraceClass `Meta.debug

@[inline] def liftMetaM [MonadLiftT MetaM m] (x : MetaM α) : m α :=
  liftM x

@[inline] def mapMetaM [MonadControlT MetaM m] [Monad m] (f : forall {α}, MetaM α → MetaM α) {α} (x : m α) : m α :=
  controlAt MetaM fun runInBase => f <| runInBase x

@[inline] def map1MetaM [MonadControlT MetaM m] [Monad m] (f : forall {α}, (β → MetaM α) → MetaM α) {α} (k : β → m α) : m α :=
  controlAt MetaM fun runInBase => f fun b => runInBase <| k b

@[inline] def map2MetaM [MonadControlT MetaM m] [Monad m] (f : forall {α}, (β → γ → MetaM α) → MetaM α) {α} (k : β → γ → m α) : m α :=
  controlAt MetaM fun runInBase => f fun b c => runInBase <| k b c

section Methods
variable [MonadControlT MetaM n] [Monad n]

@[inline] def modifyCache (f : Cache → Cache) : MetaM Unit :=
  modify fun ⟨mctx, cache, zetaFVarIds, postponed⟩ => ⟨mctx, f cache, zetaFVarIds, postponed⟩

@[inline] def modifyInferTypeCache (f : InferTypeCache → InferTypeCache) : MetaM Unit :=
  modifyCache fun ⟨ic, c1, c2, c3, c4⟩ => ⟨f ic, c1, c2, c3, c4⟩

def getLocalInstances : MetaM LocalInstances :=
  return (← read).localInstances

def getConfig : MetaM Config :=
  return (← read).config

def setMCtx (mctx : MetavarContext) : MetaM Unit :=
  modify fun s => { s with mctx := mctx }

def resetZetaFVarIds : MetaM Unit :=
  modify fun s => { s with zetaFVarIds := {} }

def getZetaFVarIds : MetaM NameSet :=
  return (← get).zetaFVarIds

def getPostponed : MetaM (PersistentArray PostponedEntry) :=
  return (← get).postponed

def setPostponed (postponed : PersistentArray PostponedEntry) : MetaM Unit :=
  modify fun s => { s with postponed := postponed }

@[inline] def modifyPostponed (f : PersistentArray PostponedEntry → PersistentArray PostponedEntry) : MetaM Unit :=
  modify fun s => { s with postponed := f s.postponed }

builtin_initialize whnfRef : IO.Ref (Expr → MetaM Expr) ← IO.mkRef fun _ => throwError "whnf implementation was not set"
builtin_initialize inferTypeRef : IO.Ref (Expr → MetaM Expr) ← IO.mkRef fun _ => throwError "inferType implementation was not set"
builtin_initialize isExprDefEqAuxRef : IO.Ref (Expr → Expr → MetaM Bool) ← IO.mkRef fun _ _ => throwError "isDefEq implementation was not set"
builtin_initialize synthPendingRef : IO.Ref (MVarId → MetaM Bool) ← IO.mkRef fun _ => pure false

def whnf (e : Expr) : MetaM Expr :=
  withIncRecDepth do (← whnfRef.get) e

def whnfForall (e : Expr) : MetaM Expr := do
  let e' ← whnf e
  if e'.isForall then pure e' else pure e

def inferType (e : Expr) : MetaM Expr :=
  withIncRecDepth do (← inferTypeRef.get) e

protected def isExprDefEqAux (t s : Expr) : MetaM Bool :=
  withIncRecDepth do (← isExprDefEqAuxRef.get) t s

protected def synthPending (mvarId : MVarId) : MetaM Bool :=
  withIncRecDepth do (← synthPendingRef.get) mvarId

-- withIncRecDepth for a monad `n` such that `[MonadControlT MetaM n]`
protected def withIncRecDepth (x : n α) : n α :=
  mapMetaM (withIncRecDepth (m := MetaM)) x

private def mkFreshExprMVarAtCore
    (mvarId : MVarId) (lctx : LocalContext) (localInsts : LocalInstances) (type : Expr) (kind : MetavarKind) (userName : Name) (numScopeArgs : Nat) : MetaM Expr := do
  modifyMCtx fun mctx => mctx.addExprMVarDecl mvarId userName lctx localInsts type kind numScopeArgs;
  return mkMVar mvarId

def mkFreshExprMVarAt
    (lctx : LocalContext) (localInsts : LocalInstances) (type : Expr)
    (kind : MetavarKind := MetavarKind.natural) (userName : Name := Name.anonymous) (numScopeArgs : Nat := 0)
    : MetaM Expr := do
  let mvarId ← mkFreshId
  mkFreshExprMVarAtCore mvarId lctx localInsts type kind userName numScopeArgs

def mkFreshLevelMVar : MetaM Level := do
  let mvarId ← mkFreshId
  modifyMCtx fun mctx => mctx.addLevelMVarDecl mvarId;
  return mkLevelMVar mvarId

private def mkFreshExprMVarCore (type : Expr) (kind : MetavarKind) (userName : Name) : MetaM Expr := do
  let lctx ← getLCtx
  let localInsts ← getLocalInstances
  mkFreshExprMVarAt lctx localInsts type kind userName

private def mkFreshExprMVarImpl (type? : Option Expr) (kind : MetavarKind) (userName : Name) : MetaM Expr :=
  match type? with
  | some type => mkFreshExprMVarCore type kind userName
  | none      => do
    let u ← mkFreshLevelMVar
    let type ← mkFreshExprMVarCore (mkSort u) MetavarKind.natural Name.anonymous
    mkFreshExprMVarCore type kind userName

def mkFreshExprMVar (type? : Option Expr) (kind := MetavarKind.natural) (userName := Name.anonymous) : MetaM Expr :=
  mkFreshExprMVarImpl type? kind userName

def mkFreshTypeMVar (kind := MetavarKind.natural) (userName := Name.anonymous) : MetaM Expr := do
  let u ← mkFreshLevelMVar
  mkFreshExprMVar (mkSort u) kind userName

/- Low-level version of `MkFreshExprMVar` which allows users to create/reserve a `mvarId` using `mkFreshId`, and then later create
   the metavar using this method. -/
private def mkFreshExprMVarWithIdCore (mvarId : MVarId) (type : Expr)
    (kind : MetavarKind := MetavarKind.natural) (userName : Name := Name.anonymous) (numScopeArgs : Nat := 0)
    : MetaM Expr := do
  let lctx ← getLCtx
  let localInsts ← getLocalInstances
  mkFreshExprMVarAtCore mvarId lctx localInsts type kind userName numScopeArgs

def mkFreshExprMVarWithId (mvarId : MVarId) (type? : Option Expr := none) (kind : MetavarKind := MetavarKind.natural) (userName := Name.anonymous) : MetaM Expr :=
  match type? with
  | some type => mkFreshExprMVarWithIdCore mvarId type kind userName
  | none      => do
    let u ← mkFreshLevelMVar
    let type ← mkFreshExprMVar (mkSort u)
    mkFreshExprMVarWithIdCore mvarId type kind userName

def mkFreshLevelMVars (num : Nat) : MetaM (List Level) :=
  num.foldM (init := []) fun _ us =>
    return (← mkFreshLevelMVar)::us

def mkFreshLevelMVarsFor (info : ConstantInfo) : MetaM (List Level) :=
  mkFreshLevelMVars info.numLevelParams

def mkConstWithFreshMVarLevels (declName : Name) : MetaM Expr := do
  let info ← getConstInfo declName
  return mkConst declName (← mkFreshLevelMVarsFor info)

def getTransparency : MetaM TransparencyMode :=
  return (← getConfig).transparency

def shouldReduceAll : MetaM Bool :=
  return (← getTransparency) == TransparencyMode.all

def shouldReduceReducibleOnly : MetaM Bool :=
  return (← getTransparency) == TransparencyMode.reducible

def getMVarDecl (mvarId : MVarId) : MetaM MetavarDecl := do
  let mctx ← getMCtx
  match mctx.findDecl? mvarId with
  | some d => pure d
  | none   => throwError "unknown metavariable '?{mvarId}'"

def setMVarKind (mvarId : MVarId) (kind : MetavarKind) : MetaM Unit :=
  modifyMCtx fun mctx => mctx.setMVarKind mvarId kind

/- Update the type of the given metavariable. This function assumes the new type is
   definitionally equal to the current one -/
def setMVarType (mvarId : MVarId) (type : Expr) : MetaM Unit := do
  modifyMCtx fun mctx => mctx.setMVarType mvarId type

def isReadOnlyExprMVar (mvarId : MVarId) : MetaM Bool := do
  let mvarDecl ← getMVarDecl mvarId
  let mctx     ← getMCtx
  return mvarDecl.depth != mctx.depth

def isReadOnlyOrSyntheticOpaqueExprMVar (mvarId : MVarId) : MetaM Bool := do
  let mvarDecl ← getMVarDecl mvarId
  match mvarDecl.kind with
  | MetavarKind.syntheticOpaque => pure true
  | _ =>
    let mctx ← getMCtx
    return mvarDecl.depth != mctx.depth

def isReadOnlyLevelMVar (mvarId : MVarId) : MetaM Bool := do
  let mctx ← getMCtx
  match mctx.findLevelDepth? mvarId with
  | some depth => return depth != mctx.depth
  | _          => throwError "unknown universe metavariable '?{mvarId}'"

def renameMVar (mvarId : MVarId) (newUserName : Name) : MetaM Unit :=
  modifyMCtx fun mctx => mctx.renameMVar mvarId newUserName

def isExprMVarAssigned (mvarId : MVarId) : MetaM Bool :=
  return (← getMCtx).isExprAssigned mvarId

def getExprMVarAssignment? (mvarId : MVarId) : MetaM (Option Expr) :=
  return (← getMCtx).getExprAssignment? mvarId

/-- Return true if `e` contains `mvarId` directly or indirectly -/
def occursCheck (mvarId : MVarId) (e : Expr) : MetaM Bool :=
  return (← getMCtx).occursCheck mvarId e

def assignExprMVar (mvarId : MVarId) (val : Expr) : MetaM Unit :=
  modifyMCtx fun mctx => mctx.assignExpr mvarId val

def isDelayedAssigned (mvarId : MVarId) : MetaM Bool :=
  return (← getMCtx).isDelayedAssigned mvarId

def getDelayedAssignment? (mvarId : MVarId) : MetaM (Option DelayedMetavarAssignment) :=
  return (← getMCtx).getDelayedAssignment? mvarId

def hasAssignableMVar (e : Expr) : MetaM Bool :=
  return (← getMCtx).hasAssignableMVar e

def throwUnknownFVar (fvarId : FVarId) : MetaM α :=
  throwError "unknown free variable '{mkFVar fvarId}'"

def findLocalDecl? (fvarId : FVarId) : MetaM (Option LocalDecl) :=
  return (← getLCtx).find? fvarId

def getLocalDecl (fvarId : FVarId) : MetaM LocalDecl := do
  match (← getLCtx).find? fvarId with
  | some d => pure d
  | none   => throwUnknownFVar fvarId

def getFVarLocalDecl (fvar : Expr) : MetaM LocalDecl :=
  getLocalDecl fvar.fvarId!

def getLocalDeclFromUserName (userName : Name) : MetaM LocalDecl := do
  match (← getLCtx).findFromUserName? userName with
  | some d => pure d
  | none   => throwError "unknown local declaration '{userName}'"

def instantiateLevelMVars (u : Level) : MetaM Level :=
  MetavarContext.instantiateLevelMVars u

def instantiateMVars (e : Expr) : MetaM Expr :=
  (MetavarContext.instantiateExprMVars e).run

def instantiateLocalDeclMVars (localDecl : LocalDecl) : MetaM LocalDecl := do
  match localDecl with
  | LocalDecl.cdecl idx id n type bi  =>
    let type ← instantiateMVars type
    return LocalDecl.cdecl idx id n type bi
  | LocalDecl.ldecl idx id n type val nonDep =>
    let type ← instantiateMVars type
    let val ← instantiateMVars val
    return LocalDecl.ldecl idx id n type val nonDep

@[inline] def liftMkBindingM (x : MetavarContext.MkBindingM α) : MetaM α := do
  match x (← getLCtx) { mctx := (← getMCtx), ngen := (← getNGen) } with
  | EStateM.Result.ok e newS => do
    setNGen newS.ngen;
    setMCtx newS.mctx;
    pure e
  | EStateM.Result.error (MetavarContext.MkBinding.Exception.revertFailure mctx lctx toRevert decl) newS => do
    setMCtx newS.mctx;
    setNGen newS.ngen;
    throwError "failed to create binder due to failure when reverting variable dependencies"

def mkForallFVars (xs : Array Expr) (e : Expr) (usedOnly : Bool := false) (usedLetOnly : Bool := true) : MetaM Expr :=
  if xs.isEmpty then pure e else liftMkBindingM <| MetavarContext.mkForall xs e usedOnly usedLetOnly

def mkLambdaFVars (xs : Array Expr) (e : Expr) (usedOnly : Bool := false) (usedLetOnly : Bool := true) : MetaM Expr :=
  if xs.isEmpty then pure e else liftMkBindingM <| MetavarContext.mkLambda xs e usedOnly usedLetOnly

def mkLetFVars (xs : Array Expr) (e : Expr) (usedLetOnly := true) : MetaM Expr :=
  mkLambdaFVars xs e (usedLetOnly := usedLetOnly)

def mkArrow (d b : Expr) : MetaM Expr := do
  let n ← mkFreshUserName `x
  return Lean.mkForall n BinderInfo.default d b

def elimMVarDeps (xs : Array Expr) (e : Expr) (preserveOrder : Bool := false) : MetaM Expr :=
  if xs.isEmpty then pure e else liftMkBindingM <| MetavarContext.elimMVarDeps xs e preserveOrder

@[inline] def withConfig (f : Config → Config) : n α → n α :=
  mapMetaM <| withReader (fun ctx => { ctx with config := f ctx.config })

@[inline] def withTrackingZeta (x : n α) : n α :=
  withConfig (fun cfg => { cfg with trackZeta := true }) x

@[inline] def withTransparency (mode : TransparencyMode) : n α → n α :=
  mapMetaM <| withConfig (fun config => { config with transparency := mode })

@[inline] def withDefault (x : n α) : n α :=
  withTransparency TransparencyMode.default x

@[inline] def withReducible (x : n α) : n α :=
  withTransparency TransparencyMode.reducible x

@[inline] def withReducibleAndInstances (x : n α) : n α :=
  withTransparency TransparencyMode.instances x

@[inline] def withAtLeastTransparency (mode : TransparencyMode) (x : n α) : n α :=
  withConfig
    (fun config =>
      let oldMode := config.transparency
      let mode    := if oldMode.lt mode then mode else oldMode
      { config with transparency := mode })
    x

/-- Save cache, execute `x`, restore cache -/
@[inline] private def savingCacheImpl (x : MetaM α) : MetaM α := do
  let s ← get
  let savedCache := s.cache
  try x finally modify fun s => { s with cache := savedCache }

@[inline] def savingCache : n α → n α :=
  mapMetaM savingCacheImpl

def getTheoremInfo (info : ConstantInfo) : MetaM (Option ConstantInfo) := do
  if (← shouldReduceAll) then
    return some info
  else
    return none

private def getDefInfoTemp (info : ConstantInfo) : MetaM (Option ConstantInfo) := do
  match (← getTransparency) with
  | TransparencyMode.all => return some info
  | TransparencyMode.default => return some info
  | _ =>
    if (← isReducible info.name) then
      return some info
    else
      return none

/- Remark: we later define `getConst?` at `GetConst.lean` after we define `Instances.lean`.
   This method is only used to implement `isClassQuickConst?`.
   It is very similar to `getConst?`, but it returns none when `TransparencyMode.instances` and
   `constName` is an instance. This difference should be irrelevant for `isClassQuickConst?`. -/
private def getConstTemp? (constName : Name) : MetaM (Option ConstantInfo) := do
  let env ← getEnv
  match env.find? constName with
  | some (info@(ConstantInfo.thmInfo _))  => getTheoremInfo info
  | some (info@(ConstantInfo.defnInfo _)) => getDefInfoTemp info
  | some info                             => pure (some info)
  | none                                  => throwUnknownConstant constName

private def isClassQuickConst? (constName : Name) : MetaM (LOption Name) := do
  let env ← getEnv
  if isClass env constName then
    pure (LOption.some constName)
  else
    match (← getConstTemp? constName) with
    | some _ => pure LOption.undef
    | none   => pure LOption.none

private partial def isClassQuick? : Expr → MetaM (LOption Name)
  | Expr.bvar ..         => pure LOption.none
  | Expr.lit ..          => pure LOption.none
  | Expr.fvar ..         => pure LOption.none
  | Expr.sort ..         => pure LOption.none
  | Expr.lam ..          => pure LOption.none
  | Expr.letE ..         => pure LOption.undef
  | Expr.proj ..         => pure LOption.undef
  | Expr.forallE _ _ b _ => isClassQuick? b
  | Expr.mdata _ e _     => isClassQuick? e
  | Expr.const n _ _     => isClassQuickConst? n
  | Expr.mvar mvarId _   => do
    match (← getExprMVarAssignment? mvarId) with
    | some val => isClassQuick? val
    | none     => pure LOption.none
  | Expr.app f _ _       =>
    match f.getAppFn with
    | Expr.const n .. => isClassQuickConst? n
    | Expr.lam ..     => pure LOption.undef
    | _              => pure LOption.none

def saveAndResetSynthInstanceCache : MetaM SynthInstanceCache := do
  let s ← get
  let savedSythInstance := s.cache.synthInstance
  modifyCache fun c => { c with synthInstance := {} }
  pure savedSythInstance

def restoreSynthInstanceCache (cache : SynthInstanceCache) : MetaM Unit :=
  modifyCache fun c => { c with synthInstance := cache }

@[inline] private def resettingSynthInstanceCacheImpl (x : MetaM α) : MetaM α := do
  let savedSythInstance ← saveAndResetSynthInstanceCache
  try x finally restoreSynthInstanceCache savedSythInstance

/-- Reset `synthInstance` cache, execute `x`, and restore cache -/
@[inline] def resettingSynthInstanceCache : n α → n α :=
  mapMetaM resettingSynthInstanceCacheImpl

@[inline] def resettingSynthInstanceCacheWhen (b : Bool) (x : n α) : n α :=
  if b then resettingSynthInstanceCache x else x

private def withNewLocalInstanceImp (className : Name) (fvar : Expr) (k : MetaM α) : MetaM α := do
  let localDecl ← getFVarLocalDecl fvar
  /- Recall that we use `auxDecl` binderInfo when compiling recursive declarations. -/
  match localDecl.binderInfo with
  | BinderInfo.auxDecl => k
  | _ =>
    resettingSynthInstanceCache <|
      withReader
        (fun ctx => { ctx with localInstances := ctx.localInstances.push { className := className, fvar := fvar } })
        k

/-- Add entry `{ className := className, fvar := fvar }` to localInstances,
    and then execute continuation `k`.
    It resets the type class cache using `resettingSynthInstanceCache`. -/
def withNewLocalInstance (className : Name) (fvar : Expr) : n α → n α :=
  mapMetaM <| withNewLocalInstanceImp className fvar

private def fvarsSizeLtMaxFVars (fvars : Array Expr) (maxFVars? : Option Nat) : Bool :=
  match maxFVars? with
  | some maxFVars => fvars.size < maxFVars
  | none          => true

mutual
  /--
    `withNewLocalInstances isClassExpensive fvars j k` updates the vector or local instances
    using free variables `fvars[j] ... fvars.back`, and execute `k`.

    - `isClassExpensive` is defined later.
    - The type class chache is reset whenever a new local instance is found.
    - `isClassExpensive` uses `whnf` which depends (indirectly) on the set of local instances.
      Thus, each new local instance requires a new `resettingSynthInstanceCache`. -/
  private partial def withNewLocalInstancesImp
      (fvars : Array Expr) (i : Nat) (k : MetaM α) : MetaM α := do
    if h : i < fvars.size then
      let fvar := fvars.get ⟨i, h⟩
      let decl ← getFVarLocalDecl fvar
      match (← isClassQuick? decl.type) with
      | LOption.none   => withNewLocalInstancesImp fvars (i+1) k
      | LOption.undef  =>
        match (← isClassExpensive? decl.type) with
        | none   => withNewLocalInstancesImp fvars (i+1) k
        | some c => withNewLocalInstance c fvar <| withNewLocalInstancesImp fvars (i+1) k
      | LOption.some c => withNewLocalInstance c fvar <| withNewLocalInstancesImp fvars (i+1) k
    else
      k

  /--
    `forallTelescopeAuxAux lctx fvars j type`
    Remarks:
    - `lctx` is the `MetaM` local context extended with declarations for `fvars`.
    - `type` is the type we are computing the telescope for. It contains only
      dangling bound variables in the range `[j, fvars.size)`
    - if `reducing? == true` and `type` is not `forallE`, we use `whnf`.
    - when `type` is not a `forallE` nor it can't be reduced to one, we
      excute the continuation `k`.

    Here is an example that demonstrates the `reducing?`.
    Suppose we have
    ```
    abbrev StateM s a := s -> Prod a s
    ```
    Now, assume we are trying to build the telescope for
    ```
    forall (x : Nat), StateM Int Bool
    ```
    if `reducing == true`, the function executes `k #[(x : Nat) (s : Int)] Bool`.
    if `reducing == false`, the function executes `k #[(x : Nat)] (StateM Int Bool)`

    if `maxFVars?` is `some max`, then we interrupt the telescope construction
    when `fvars.size == max`
  -/
  private partial def forallTelescopeReducingAuxAux
      (reducing          : Bool) (maxFVars? : Option Nat)
      (type              : Expr)
      (k                 : Array Expr → Expr → MetaM α) : MetaM α := do
    let rec process (lctx : LocalContext) (fvars : Array Expr) (j : Nat) (type : Expr) : MetaM α := do
      match type with
      | Expr.forallE n d b c =>
        if fvarsSizeLtMaxFVars fvars maxFVars? then
          let d     := d.instantiateRevRange j fvars.size fvars
          let fvarId ← mkFreshId
          let lctx  := lctx.mkLocalDecl fvarId n d c.binderInfo
          let fvar  := mkFVar fvarId
          let fvars := fvars.push fvar
          process lctx fvars j b
        else
          let type := type.instantiateRevRange j fvars.size fvars;
          withReader (fun ctx => { ctx with lctx := lctx }) do
            withNewLocalInstancesImp fvars j do
              k fvars type
      | _ =>
        let type := type.instantiateRevRange j fvars.size fvars;
        withReader (fun ctx => { ctx with lctx := lctx }) do
          withNewLocalInstancesImp fvars j do
            if reducing && fvarsSizeLtMaxFVars fvars maxFVars? then
              let newType ← whnf type
              if newType.isForall then
                process lctx fvars fvars.size newType
              else
                k fvars type
            else
              k fvars type
    process (← getLCtx) #[] 0 type

  private partial def forallTelescopeReducingAux (type : Expr) (maxFVars? : Option Nat) (k : Array Expr → Expr → MetaM α) : MetaM α := do
    match maxFVars? with
    | some 0 => k #[] type
    | _ => do
      let newType ← whnf type
      if newType.isForall then
        forallTelescopeReducingAuxAux true maxFVars? newType k
      else
        k #[] type

  private partial def isClassExpensive? : Expr → MetaM (Option Name)
    | type => withReducible <| -- when testing whether a type is a type class, we only unfold reducible constants.
      forallTelescopeReducingAux type none fun xs type => do
        let env ← getEnv
        match type.getAppFn with
        | Expr.const c _ _ => do
          if isClass env c then
            return some c
          else
            -- make sure abbreviations are unfolded
            match (← whnf type).getAppFn with
            | Expr.const c _ _ => return if isClass env c then some c else none
            | _ => return none
        | _ => return none

  private partial def isClassImp? (type : Expr) : MetaM (Option Name) := do
    match (← isClassQuick? type) with
    | LOption.none   => pure none
    | LOption.some c => pure (some c)
    | LOption.undef  => isClassExpensive? type

end

def isClass? (type : Expr) : MetaM (Option Name) :=
  try isClassImp? type catch _ => pure none

private def withNewLocalInstancesImpAux (fvars : Array Expr) (j : Nat) : n α → n α :=
  mapMetaM <| withNewLocalInstancesImp fvars j

partial def withNewLocalInstances (fvars : Array Expr) (j : Nat) : n α → n α :=
  mapMetaM <| withNewLocalInstancesImpAux fvars j

@[inline] private def forallTelescopeImp (type : Expr) (k : Array Expr → Expr → MetaM α) : MetaM α := do
  forallTelescopeReducingAuxAux (reducing := false) (maxFVars? := none) type k

/--
  Given `type` of the form `forall xs, A`, execute `k xs A`.
  This combinator will declare local declarations, create free variables for them,
  execute `k` with updated local context, and make sure the cache is restored after executing `k`. -/
def forallTelescope (type : Expr) (k : Array Expr → Expr → n α) : n α :=
  map2MetaM (fun k => forallTelescopeImp type k) k

private def forallTelescopeReducingImp (type : Expr) (k : Array Expr → Expr → MetaM α) : MetaM α :=
  forallTelescopeReducingAux type (maxFVars? := none) k

/--
  Similar to `forallTelescope`, but given `type` of the form `forall xs, A`,
  it reduces `A` and continues bulding the telescope if it is a `forall`. -/
def forallTelescopeReducing (type : Expr) (k : Array Expr → Expr → n α) : n α :=
  map2MetaM (fun k => forallTelescopeReducingImp type k) k

private def forallBoundedTelescopeImp (type : Expr) (maxFVars? : Option Nat) (k : Array Expr → Expr → MetaM α) : MetaM α :=
  forallTelescopeReducingAux type maxFVars? k

/--
  Similar to `forallTelescopeReducing`, stops constructing the telescope when
  it reaches size `maxFVars`. -/
def forallBoundedTelescope (type : Expr) (maxFVars? : Option Nat) (k : Array Expr → Expr → n α) : n α :=
  map2MetaM (fun k => forallBoundedTelescopeImp type maxFVars? k) k

/-- Similar to `forallTelescopeAuxAux` but for lambda and let expressions. -/
private partial def lambdaTelescopeAux
    (k : Array Expr → Expr → MetaM α)
    : Bool → LocalContext → Array Expr → Nat → Expr → MetaM α
  | consumeLet, lctx, fvars, j, Expr.lam n d b c => do
    let d := d.instantiateRevRange j fvars.size fvars
    let fvarId ← mkFreshId
    let lctx := lctx.mkLocalDecl fvarId n d c.binderInfo
    let fvar := mkFVar fvarId
    lambdaTelescopeAux k consumeLet lctx (fvars.push fvar) j b
  | true, lctx, fvars, j, Expr.letE n t v b _ => do
    let t := t.instantiateRevRange j fvars.size fvars
    let v := v.instantiateRevRange j fvars.size fvars
    let fvarId ← mkFreshId
    let lctx := lctx.mkLetDecl fvarId n t v
    let fvar := mkFVar fvarId
    lambdaTelescopeAux k true lctx (fvars.push fvar) j b
  | _, lctx, fvars, j, e =>
    let e := e.instantiateRevRange j fvars.size fvars;
    withReader (fun ctx => { ctx with lctx := lctx }) do
      withNewLocalInstancesImp fvars j do
        k fvars e

private partial def lambdaTelescopeImp (e : Expr) (consumeLet : Bool) (k : Array Expr → Expr → MetaM α) : MetaM α := do
  let rec process (consumeLet : Bool) (lctx : LocalContext) (fvars : Array Expr) (j : Nat) (e : Expr) : MetaM α := do
    match consumeLet, e with
    | _, Expr.lam n d b c =>
      let d := d.instantiateRevRange j fvars.size fvars
      let fvarId ← mkFreshId
      let lctx := lctx.mkLocalDecl fvarId n d c.binderInfo
      let fvar := mkFVar fvarId
      process consumeLet lctx (fvars.push fvar) j b
    | true, Expr.letE n t v b _ => do
      let t := t.instantiateRevRange j fvars.size fvars
      let v := v.instantiateRevRange j fvars.size fvars
      let fvarId ← mkFreshId
      let lctx := lctx.mkLetDecl fvarId n t v
      let fvar := mkFVar fvarId
      process true lctx (fvars.push fvar) j b
    | _, e =>
      let e := e.instantiateRevRange j fvars.size fvars
      withReader (fun ctx => { ctx with lctx := lctx }) do
        withNewLocalInstancesImp fvars j do
          k fvars e
  process consumeLet (← getLCtx) #[] 0 e

/-- Similar to `forallTelescope` but for lambda and let expressions. -/
def lambdaLetTelescope (type : Expr) (k : Array Expr → Expr → n α) : n α :=
  map2MetaM (fun k => lambdaTelescopeImp type true k) k

/-- Similar to `forallTelescope` but for lambda expressions. -/
def lambdaTelescope (type : Expr) (k : Array Expr → Expr → n α) : n α :=
  map2MetaM (fun k => lambdaTelescopeImp type false k) k

/-- Return the parameter names for the givel global declaration. -/
def getParamNames (declName : Name) : MetaM (Array Name) := do
  let cinfo ← getConstInfo declName
  forallTelescopeReducing cinfo.type fun xs _ => do
    xs.mapM fun x => do
      let localDecl ← getLocalDecl x.fvarId!
      pure localDecl.userName

-- `kind` specifies the metavariable kind for metavariables not corresponding to instance implicit `[ ... ]` arguments.
private partial def forallMetaTelescopeReducingAux
    (e : Expr) (reducing : Bool) (maxMVars? : Option Nat) (kind : MetavarKind) : MetaM (Array Expr × Array BinderInfo × Expr) :=
  let rec process (mvars : Array Expr) (bis : Array BinderInfo) (j : Nat) (type : Expr) : MetaM (Array Expr × Array BinderInfo × Expr) := do
    match type with
    | Expr.forallE n d b c =>
      let cont : Unit → MetaM (Array Expr × Array BinderInfo × Expr) := fun _ => do
        let d  := d.instantiateRevRange j mvars.size mvars
        let k  := if c.binderInfo.isInstImplicit then  MetavarKind.synthetic else kind
        let mvar ← mkFreshExprMVar d k n
        let mvars := mvars.push mvar
        let bis   := bis.push c.binderInfo
        process mvars bis j b
      match maxMVars? with
      | none          => cont ()
      | some maxMVars =>
        if mvars.size < maxMVars then
          cont ()
        else
          let type := type.instantiateRevRange j mvars.size mvars;
          pure (mvars, bis, type)
    | _ =>
      let type := type.instantiateRevRange j mvars.size mvars;
      if reducing then do
        let newType ← whnf type;
        if newType.isForall then
          process mvars bis mvars.size newType
        else
          pure (mvars, bis, type)
      else
        pure (mvars, bis, type)
  process #[] #[] 0 e

/-- Similar to `forallTelescope`, but creates metavariables instead of free variables. -/
def forallMetaTelescope (e : Expr) (kind := MetavarKind.natural) : MetaM (Array Expr × Array BinderInfo × Expr) :=
  forallMetaTelescopeReducingAux e (reducing := false) (maxMVars? := none) kind

/-- Similar to `forallTelescopeReducing`, but creates metavariables instead of free variables. -/
def forallMetaTelescopeReducing (e : Expr) (maxMVars? : Option Nat := none) (kind := MetavarKind.natural) : MetaM (Array Expr × Array BinderInfo × Expr) :=
  forallMetaTelescopeReducingAux e (reducing := true) maxMVars? kind

/-- Similar to `forallMetaTelescopeReducingAux` but for lambda expressions. -/
partial def lambdaMetaTelescope (e : Expr) (maxMVars? : Option Nat := none) : MetaM (Array Expr × Array BinderInfo × Expr) :=
  let rec process (mvars : Array Expr) (bis : Array BinderInfo) (j : Nat) (type : Expr) : MetaM (Array Expr × Array BinderInfo × Expr) := do
    let finalize : Unit → MetaM (Array Expr × Array BinderInfo × Expr) := fun _ => do
      let type := type.instantiateRevRange j mvars.size mvars
      pure (mvars, bis, type)
    let cont : Unit → MetaM (Array Expr × Array BinderInfo × Expr) := fun _ => do
      match type with
      | Expr.lam n d b c =>
        let d     := d.instantiateRevRange j mvars.size mvars
        let mvar ← mkFreshExprMVar d
        let mvars := mvars.push mvar
        let bis   := bis.push c.binderInfo
        process mvars bis j b
      | _ => finalize ()
    match maxMVars? with
    | none          => cont ()
    | some maxMVars =>
      if mvars.size < maxMVars then
        cont ()
      else
        finalize ()
  process #[] #[] 0 e

private def withNewFVar (fvar fvarType : Expr) (k : Expr → MetaM α) : MetaM α := do
  match (← isClass? fvarType) with
  | none   => k fvar
  | some c => withNewLocalInstance c fvar <| k fvar

private def withLocalDeclImp (n : Name) (bi : BinderInfo) (type : Expr) (k : Expr → MetaM α) : MetaM α := do
  let fvarId ← mkFreshId
  let ctx ← read
  let lctx := ctx.lctx.mkLocalDecl fvarId n type bi
  let fvar := mkFVar fvarId
  withReader (fun ctx => { ctx with lctx := lctx }) do
    withNewFVar fvar type k

def withLocalDecl (name : Name) (bi : BinderInfo) (type : Expr) (k : Expr → n α) : n α :=
  map1MetaM (fun k => withLocalDeclImp name bi type k) k

def withLocalDeclD (name : Name) (type : Expr) (k : Expr → n α) : n α :=
  withLocalDecl name BinderInfo.default type k

partial def withLocalDecls
    [Inhabited α]
    (declInfos : Array (Name × BinderInfo × (Array Expr → n Expr)))
    (k : (xs : Array Expr) → n α)
    : n α :=
  let rec loop
      [Inhabited α]
      (acc : Array Expr) : n α := do
    if acc.size < declInfos.size then
      let (name, bi, typeCtor) := declInfos[acc.size]
      withLocalDecl name bi (←typeCtor acc) fun x => loop (acc.push x)
    else k acc

  loop #[]

def withLocalDeclsD
    [Inhabited α]
    (declInfos : Array (Name × (Array Expr → n Expr)))
    (k : (xs : Array Expr) → n α)
    : n α :=
  withLocalDecls
    (declInfos.map (fun (name, typeCtor) => (name, BinderInfo.default, typeCtor))) k

private def withNewBinderInfosImp (bs : Array (FVarId × BinderInfo)) (k : MetaM α) : MetaM α := do
  let lctx := bs.foldl (init := (← getLCtx)) fun lctx (fvarId, bi) =>
      lctx.setBinderInfo fvarId bi
  withReader (fun ctx => { ctx with lctx := lctx }) k

def withNewBinderInfos (bs : Array (FVarId × BinderInfo)) (k : n α) : n α :=
  mapMetaM (fun k => withNewBinderInfosImp bs k) k

private def withLetDeclImp (n : Name) (type : Expr) (val : Expr) (k : Expr → MetaM α) : MetaM α := do
  let fvarId ← mkFreshId
  let ctx ← read
  let lctx := ctx.lctx.mkLetDecl fvarId n type val
  let fvar := mkFVar fvarId
  withReader (fun ctx => { ctx with lctx := lctx }) do
    withNewFVar fvar type k

def withLetDecl (name : Name) (type : Expr) (val : Expr) (k : Expr → n α) : n α :=
  map1MetaM (fun k => withLetDeclImp name type val k) k

private def withExistingLocalDeclsImp (decls : List LocalDecl) (k : MetaM α) : MetaM α := do
  let ctx ← read
  let numLocalInstances := ctx.localInstances.size
  let lctx := decls.foldl (fun (lctx : LocalContext) decl => lctx.addDecl decl) ctx.lctx
  withReader (fun ctx => { ctx with lctx := lctx }) do
    let newLocalInsts ← decls.foldlM
      (fun (newlocalInsts : Array LocalInstance) (decl : LocalDecl) => (do {
        match (← isClass? decl.type) with
        | none   => pure newlocalInsts
        | some c => pure <| newlocalInsts.push { className := c, fvar := decl.toExpr } } : MetaM _))
      ctx.localInstances;
    if newLocalInsts.size == numLocalInstances then
      k
    else
      resettingSynthInstanceCache <| withReader (fun ctx => { ctx with localInstances := newLocalInsts }) k

def withExistingLocalDecls (decls : List LocalDecl) : n α → n α :=
  mapMetaM <| withExistingLocalDeclsImp decls

private def withNewMCtxDepthImp (x : MetaM α) : MetaM α := do
  let saved ← get
  modify fun s => { s with mctx := s.mctx.incDepth, postponed := {} }
  try
    x
  finally
    modify fun s => { s with mctx := saved.mctx, postponed := saved.postponed }

/--
  Save cache and `MetavarContext`, bump the `MetavarContext` depth, execute `x`,
  and restore saved data. -/
def withNewMCtxDepth : n α → n α :=
  mapMetaM withNewMCtxDepthImp

private def withLocalContextImp (lctx : LocalContext) (localInsts : LocalInstances) (x : MetaM α) : MetaM α := do
  let localInstsCurr ← getLocalInstances
  withReader (fun ctx => { ctx with lctx := lctx, localInstances := localInsts }) do
    if localInsts == localInstsCurr then
      x
    else
      resettingSynthInstanceCache x

def withLCtx (lctx : LocalContext) (localInsts : LocalInstances) : n α → n α :=
  mapMetaM <| withLocalContextImp lctx localInsts

private def withMVarContextImp (mvarId : MVarId) (x : MetaM α) : MetaM α := do
  let mvarDecl ← getMVarDecl mvarId
  withLocalContextImp mvarDecl.lctx mvarDecl.localInstances x

/--
  Execute `x` using the given metavariable `LocalContext` and `LocalInstances`.
  The type class resolution cache is flushed when executing `x` if its `LocalInstances` are
  different from the current ones. -/
def withMVarContext (mvarId : MVarId) : n α → n α :=
  mapMetaM <| withMVarContextImp mvarId

private def withMCtxImp (mctx : MetavarContext) (x : MetaM α) : MetaM α := do
  let mctx' ← getMCtx
  setMCtx mctx
  try x finally setMCtx mctx'

def withMCtx (mctx : MetavarContext) : n α → n α :=
  mapMetaM <| withMCtxImp mctx

@[inline] private def approxDefEqImp (x : MetaM α) : MetaM α :=
  withConfig (fun config => { config with foApprox := true, ctxApprox := true, quasiPatternApprox := true}) x

/-- Execute `x` using approximate unification: `foApprox`, `ctxApprox` and `quasiPatternApprox`.  -/
@[inline] def approxDefEq : n α → n α :=
  mapMetaM approxDefEqImp

@[inline] private def fullApproxDefEqImp (x : MetaM α) : MetaM α :=
  withConfig (fun config => { config with foApprox := true, ctxApprox := true, quasiPatternApprox := true, constApprox := true }) x

/--
  Similar to `approxDefEq`, but uses all available approximations.
  We don't use `constApprox` by default at `approxDefEq` because it often produces undesirable solution for monadic code.
  For example, suppose we have `pure (x > 0)` which has type `?m Prop`. We also have the goal `[Pure ?m]`.
  Now, assume the expected type is `IO Bool`. Then, the unification constraint `?m Prop =?= IO Bool` could be solved
  as `?m := fun _ => IO Bool` using `constApprox`, but this spurious solution would generate a failure when we try to
  solve `[Pure (fun _ => IO Bool)]` -/
@[inline] def fullApproxDefEq : n α → n α :=
  mapMetaM fullApproxDefEqImp

def normalizeLevel (u : Level) : MetaM Level := do
  let u ← instantiateLevelMVars u
  pure u.normalize

def assignLevelMVar (mvarId : MVarId) (u : Level) : MetaM Unit := do
  modifyMCtx fun mctx => mctx.assignLevel mvarId u

def whnfR (e : Expr) : MetaM Expr :=
  withTransparency TransparencyMode.reducible <| whnf e

def whnfD (e : Expr) : MetaM Expr :=
  withTransparency TransparencyMode.default <| whnf e

def whnfI (e : Expr) : MetaM Expr :=
  withTransparency TransparencyMode.instances <| whnf e

def setInlineAttribute (declName : Name) (kind := Compiler.InlineAttributeKind.inline): MetaM Unit := do
  let env ← getEnv
  match Compiler.setInlineAttribute env declName kind with
  | Except.ok env    => setEnv env
  | Except.error msg => throwError msg

private partial def instantiateForallAux (ps : Array Expr) (i : Nat) (e : Expr) : MetaM Expr := do
  if h : i < ps.size then
    let p := ps.get ⟨i, h⟩
    let e ← whnf e
    match e with
    | Expr.forallE _ _ b _ => instantiateForallAux ps (i+1) (b.instantiate1 p)
    | _                    => throwError "invalid instantiateForall, too many parameters"
  else
    pure e

/- Given `e` of the form `forall (a_1 : A_1) ... (a_n : A_n), B[a_1, ..., a_n]` and `p_1 : A_1, ... p_n : A_n`, return `B[p_1, ..., p_n]`. -/
def instantiateForall (e : Expr) (ps : Array Expr) : MetaM Expr :=
  instantiateForallAux ps 0 e

private partial def instantiateLambdaAux (ps : Array Expr) (i : Nat) (e : Expr) : MetaM Expr := do
  if h : i < ps.size then
    let p := ps.get ⟨i, h⟩
    let e ← whnf e
    match e with
    | Expr.lam _ _ b _ => instantiateLambdaAux ps (i+1) (b.instantiate1 p)
    | _                => throwError "invalid instantiateLambda, too many parameters"
  else
    pure e

/- Given `e` of the form `fun (a_1 : A_1) ... (a_n : A_n) => t[a_1, ..., a_n]` and `p_1 : A_1, ... p_n : A_n`, return `t[p_1, ..., p_n]`.
   It uses `whnf` to reduce `e` if it is not a lambda -/
def instantiateLambda (e : Expr) (ps : Array Expr) : MetaM Expr :=
  instantiateLambdaAux ps 0 e

/-- Return true iff `e` depends on the free variable `fvarId` -/
def dependsOn (e : Expr) (fvarId : FVarId) : MetaM Bool :=
  return (← getMCtx).exprDependsOn e fvarId

def ppExpr (e : Expr) : MetaM Format := do
  let env  ← getEnv
  let mctx ← getMCtx
  let lctx ← getLCtx
  let opts ← getOptions
  let ctxCore  ← readThe Core.Context
  Lean.ppExpr { env := env, mctx := mctx, lctx := lctx, opts := opts, currNamespace := ctxCore.currNamespace, openDecls := ctxCore.openDecls  } e

@[inline] protected def orelse (x y : MetaM α) : MetaM α := do
  let env  ← getEnv
  let mctx ← getMCtx
  try x catch _ => setEnv env; setMCtx mctx; y

instance : OrElse (MetaM α) := ⟨Meta.orelse⟩

@[inline] private def orelseMergeErrorsImp (x y : MetaM α)
    (mergeRef : Syntax → Syntax → Syntax := fun r₁ r₂ => r₁)
    (mergeMsg : MessageData → MessageData → MessageData := fun m₁ m₂ => m₁ ++ Format.line ++ m₂) : MetaM α := do
  let env  ← getEnv
  let mctx ← getMCtx
  try
    x
  catch ex =>
    setEnv env
    setMCtx mctx
    match ex with
    | Exception.error ref₁ m₁ =>
      try
        y
      catch
        | Exception.error ref₂ m₂ => throw <| Exception.error (mergeRef ref₁ ref₂) (mergeMsg m₁ m₂)
        | ex => throw ex
    | ex => throw ex

/--
  Similar to `orelse`, but merge errors. Note that internal errors are not caught.
  The default `mergeRef` uses the `ref` (position information) for the first message.
  The default `mergeMsg` combines error messages using `Format.line ++ Format.line` as a separator. -/
@[inline] def orelseMergeErrors [MonadControlT MetaM m] [Monad m] (x y : m α)
    (mergeRef : Syntax → Syntax → Syntax := fun r₁ r₂ => r₁)
    (mergeMsg : MessageData → MessageData → MessageData := fun m₁ m₂ => m₁ ++ Format.line ++ Format.line ++ m₂) : m α := do
  controlAt MetaM fun runInBase => orelseMergeErrorsImp (runInBase x) (runInBase y) mergeRef mergeMsg

/-- Execute `x`, and apply `f` to the produced error message -/
def mapErrorImp (x : MetaM α) (f : MessageData → MessageData) : MetaM α := do
  try
    x
  catch
    | Exception.error ref msg => throw <| Exception.error ref <| f msg
    | ex => throw ex

@[inline] def mapError [MonadControlT MetaM m] [Monad m] (x : m α) (f : MessageData → MessageData) : m α :=
  controlAt MetaM fun runInBase => mapErrorImp (runInBase x) f

end Methods
end Meta

export Meta (MetaM)

end Lean
