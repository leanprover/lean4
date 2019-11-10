/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Control.Reader
import Init.Lean.NameGenerator
import Init.Lean.Environment
import Init.Lean.LOption
import Init.Lean.Trace
import Init.Lean.AuxRecursor
import Init.Lean.Class
import Init.Lean.WHNF
import Init.Lean.ReducibilityAttrs

/-
This module provides four (mutually dependent) goodies that are needed for building the elaborator and tactic frameworks.
1- Weak head normal form computation with support for metavariables and transparency modes.
2- Definitionally equality checking with support for metavariables (aka unification modulo definitional equality).
3- Type inference.
4- Type class resolution.

They are packed into the MetaM monad.
-/

namespace Lean
namespace Meta

inductive TransparencyMode
| all | default | reducible

namespace TransparencyMode
instance : Inhabited TransparencyMode := ⟨TransparencyMode.default⟩

def beq : TransparencyMode → TransparencyMode → Bool
| all,       all       => true
| default,   default   => true
| reducible, reducible => true
| _,         _         => false

instance : HasBeq TransparencyMode := ⟨beq⟩

def hash : TransparencyMode → USize
| all       => 7
| default   => 11
| reducible => 13

instance : Hashable TransparencyMode := ⟨hash⟩

end TransparencyMode

structure LocalInstance :=
(className : Name)
(fvar      : Expr)

abbrev LocalInstances := Array LocalInstance

structure Config :=
(opts               : Options := {})
(foApprox           : Bool    := false)
(ctxApprox          : Bool    := false)
(quasiPatternApprox : Bool    := false)
(debug              : Bool    := false)
(transparency       : TransparencyMode := TransparencyMode.default)

structure Cache :=
(whnf      : PersistentHashMap (TransparencyMode × Expr) Expr := {})
(inferType : PersistentHashMap Expr Expr := {})

structure ExceptionContext :=
(env : Environment) (mctx : MetavarContext) (lctx : LocalContext)

inductive Bug
| overwritingExprMVar (mvarId : Name)

inductive Exception
| unknownConst         (constName : Name) (ctx : ExceptionContext)
| unknownFVar          (fvarId : Name) (ctx : ExceptionContext)
| unknownMVar          (mvarId : Name) (ctx : ExceptionContext)
| functionExpected     (fType : Expr) (args : Array Expr) (ctx : ExceptionContext)
| typeExpected         (type : Expr) (ctx : ExceptionContext)
| incorrectNumOfLevels (constName : Name) (constLvls : List Level) (ctx : ExceptionContext)
| invalidProjection    (structName : Name) (idx : Nat) (s : Expr) (ctx : ExceptionContext)
| revertFailure        (toRevert : Array Expr) (decl : LocalDecl) (ctx : ExceptionContext)
| readOnlyMVar         (mvarId : Name) (ctx : ExceptionContext)
| bug                  (b : Bug) (ctx : ExceptionContext)
| other                (msg : String)

instance Exception.inhabited : Inhabited Exception := ⟨Exception.other ""⟩

structure Context :=
(config         : Config         := {})
(lctx           : LocalContext   := {})
(localInstances : LocalInstances := #[])

structure PostponedEntry :=
(lhs       : Level)
(updateLhs : Bool)
(rhs       : Level)
(updateRhs : Bool)

structure State :=
(env            : Environment)
(mctx           : MetavarContext       := {})
(cache          : Cache                := {})
(ngen           : NameGenerator        := {})
(traceState     : TraceState           := {})
(postponed      : PersistentArray PostponedEntry := {})

abbrev MetaM := ReaderT Context (EStateM Exception State)

instance MetaM.inhabited {α} : Inhabited (MetaM α) :=
⟨fun c s => EStateM.Result.error (arbitrary _) s⟩

@[inline] private def getLCtx : MetaM LocalContext :=
do ctx ← read; pure ctx.lctx

@[inline] private def getMCtx : MetaM MetavarContext :=
do s ← get; pure s.mctx

@[inline] private def getEnv : MetaM Environment :=
do s ← get; pure s.env

@[inline] private def throwEx {α} (f : ExceptionContext → Exception) : MetaM α :=
do ctx ← read;
   s ← get;
   throw (f {env := s.env, mctx := s.mctx, lctx := ctx.lctx })

@[inline] private def throwBug {α} (b : Bug) : MetaM α :=
throwEx $ Exception.bug b

/-- Execute `x` only in debugging mode. -/
@[inline] private def whenDebugging {α} (x : MetaM α) : MetaM Unit :=
do ctx ← read;
   when ctx.config.debug (do x; pure ())

private def mkFreshId : MetaM Name :=
do s ← get;
   let id := s.ngen.curr;
   modify $ fun s => { ngen := s.ngen.next, .. s };
   pure id

@[inline] private def reduceAll? : MetaM Bool :=
do ctx ← read; pure $ ctx.config.transparency == TransparencyMode.all

@[inline] private def reduceReducibleOnly? : MetaM Bool :=
do ctx ← read; pure $ ctx.config.transparency == TransparencyMode.reducible

@[inline] private def getTransparency : MetaM TransparencyMode :=
do ctx ← read; pure $ ctx.config.transparency

@[inline] private def getOptions : MetaM Options :=
do ctx ← read; pure ctx.config.opts

-- Remark: wanted to use `private`, but in C++ parser, `private` declarations do not shadow outer public ones.
-- TODO: fix this bug
@[inline] def isReducible (constName : Name) : MetaM Bool :=
do env ← getEnv; pure $ isReducible env constName

/-- While executing `x`, Ensure only constants tagged as [reducible] are unfolded. -/
@[inline] def byUnfoldingReducibleOnly {α} (x : MetaM α) : MetaM α :=
adaptReader
  (fun (ctx : Context) => { config := { transparency := TransparencyMode.reducible, .. ctx.config }, .. ctx })
  x

private def isReadOnlyOrSyntheticMVar (mvarId : Name) : MetaM Bool :=
do mctx ← getMCtx;
   match mctx.findDecl mvarId with
   | some d => pure $ d.synthetic || d.depth != mctx.depth
   | _      => throwEx $ Exception.unknownMVar mvarId

@[inline] private def isExprAssigned (mvarId : Name) : MetaM Bool :=
do mctx ← getMCtx;
   pure $ mctx.isExprAssigned mvarId

@[inline] private def getMVarAssignment (mvarId : Name) : MetaM (Option Expr) :=
do mctx ← getMCtx; pure (mctx.getExprAssignment mvarId)

private def assignExprMVar (mvarId : Name) (val : Expr) : MetaM Unit :=
do whenDebugging $ whenM (isExprAssigned mvarId) $ throwBug $ Bug.overwritingExprMVar mvarId;
   modify $ fun s => { mctx := s.mctx.assignExpr mvarId val, .. s }

@[inline] private def getTraceState : MetaM TraceState :=
do s ← get; pure s.traceState

instance tracer : SimpleMonadTracerAdapter MetaM :=
{ getOptions       := getOptions,
  getTraceState    := getTraceState,
  modifyTraceState := fun f => modify $ fun s => { traceState := f s.traceState, .. s } }

private def getConst (constName : Name) : MetaM (Option ConstantInfo) :=
do env ← getEnv;
   match env.find constName with
   | some (info@(ConstantInfo.thmInfo _)) =>
     condM reduceAll? (pure (some info)) (pure none)
   | some info                            =>
     condM reduceReducibleOnly?
       (condM (isReducible constName) (pure (some info)) (pure none))
       (pure (some info))
   | none                                 =>
     throwEx $ Exception.unknownConst constName

private def isAuxDef? (constName : Name) : MetaM Bool :=
do env ← getEnv; pure (isAuxRecursor env constName || isNoConfusion env constName)

private def getLocalDecl (fvarId : Name) : MetaM LocalDecl :=
do lctx ← getLCtx;
   match lctx.find fvarId with
   | some d => pure d
   | none   => throwEx $ Exception.unknownFVar fvarId

@[inline] private def getCachedWHNF (e : Expr) : MetaM (Option Expr) :=
do t ← getTransparency;
   s ← get;
   pure $ s.cache.whnf.find (t, e)

@[inline] private def cacheWHNF (e : Expr) (r : Expr) : MetaM Unit :=
do t ← getTransparency;
   modify $ fun s => { cache := { whnf := s.cache.whnf.insert (t, e) r, .. s.cache }, .. s }

def instantiateMVars (e : Expr) : MetaM Expr :=
if e.hasMVar then
  modifyGet $ fun s =>
    let (e, mctx) := s.mctx.instantiateMVars e;
    (e, { mctx := mctx, .. s })
else
  pure e

@[specialize] private partial def whnfAux
    (inferType         : Expr → MetaM Expr)
    (isDefEq           : Expr → Expr → MetaM Bool)
    (synthesizePending : Expr → MetaM Bool)
    : Expr → MetaM Expr
| e => whnfEasyCases getLocalDecl getMVarAssignment e $ fun e => do
  cached? ← getCachedWHNF e;
  match cached? with
  | some r => pure r
  | none   => do
    e ← whnfCore getConst isAuxDef? whnfAux inferType isDefEq getLocalDecl getMVarAssignment e;
    r ← unfoldDefinition getConst isAuxDef? whnfAux inferType isDefEq synthesizePending getLocalDecl getMVarAssignment e (fun _ => pure e) whnfAux;
    cacheWHNF e r;
    pure r

@[inline] private def liftMkBindingM {α} (x : MetavarContext.MkBindingM α) : MetaM α :=
fun ctx s =>
  match x ctx.lctx { mctx := s.mctx, ngen := s.ngen } with
  | EStateM.Result.ok e newS      =>
    EStateM.Result.ok e { mctx := newS.mctx, ngen := newS.ngen, .. s}
  | EStateM.Result.error (MetavarContext.MkBinding.Exception.readOnlyMVar mctx mvarId) newS =>
    EStateM.Result.error
      (Exception.readOnlyMVar mvarId { lctx := ctx.lctx, mctx := newS.mctx, env := s.env })
      { mctx := newS.mctx, ngen := newS.ngen, .. s }
  | EStateM.Result.error (MetavarContext.MkBinding.Exception.revertFailure mctx lctx toRevert decl) newS =>
    EStateM.Result.error
      (Exception.revertFailure toRevert decl { lctx := lctx, mctx := mctx, env := s.env })
      { mctx := newS.mctx, ngen := newS.ngen, .. s }

def mkForall (xs : Array Expr) (e : Expr) : MetaM Expr :=
liftMkBindingM $ MetavarContext.mkForall xs e

def mkLambda (xs : Array Expr) (e : Expr) : MetaM Expr :=
liftMkBindingM $ MetavarContext.mkLambda xs e

/-- Save cache, execute `x`, restore cache -/
@[inline] private def savingCache {α} (x : MetaM α) : MetaM α :=
do s ← get;
   let savedCache := s.cache;
   finally x (modify $ fun s => { cache := savedCache, .. s })

def isClassQuickConst (constName : Name) : MetaM (LOption Name) :=
do env ← getEnv;
   if isClass env constName then
     pure (LOption.some constName)
   else do
     cinfo? ← getConst constName;
     match cinfo? with
     | some _ => pure LOption.undef
     | none   => pure LOption.none

private partial def isClassQuick : Expr → MetaM (LOption Name)
| Expr.bvar _          => pure LOption.none
| Expr.lit _           => pure LOption.none
| Expr.fvar _          => pure LOption.none
| Expr.sort _          => pure LOption.none
| Expr.lam _ _ _ _     => pure LOption.none
| Expr.letE _ _ _ _    => pure LOption.undef
| Expr.proj _ _ _      => pure LOption.undef
| Expr.forallE _ _ _ b => isClassQuick b
| Expr.mdata _ e       => isClassQuick e
| Expr.const n _       => isClassQuickConst n
| Expr.mvar mvarId     => do
  val? ← getMVarAssignment mvarId;
  match val? with
  | some val => isClassQuick val
  | none     => pure LOption.none
| Expr.app f _         =>
  match f.getAppFn with
  | Expr.const n _   => isClassQuickConst n
  | Expr.lam _ _ _ _ => pure LOption.undef
  | _                => pure LOption.none

/-- Reset type class cache, execute `x`, and restore cache -/
@[inline] private def resettingTypeClassCache {α} (x : MetaM α) : MetaM α :=
x -- TODO

/--
  `withNewLocalInstances isClassExpensive fvars j k` updates the vector or local instances
  using free variables `fvars[j] ... fvars.back`, and execute `k`.

  - `isClassExpensive` is defined later.
  - The type class chache is reset whenever a new local instance is found.
  - `isClassExpensive` uses `whnf` which depends (indirectly) on the set of local instances.
    Thus, each new local instance requires a new `resettingTypeClassCache`. -/
@[specialize] private partial def withNewLocalInstances {α}
    (isClassExpensive : Expr → MetaM (Option Name))
    (fvars : Array Expr) : Nat → MetaM α → MetaM α
| i, k =>
  if h : i < fvars.size then do
    let fvar := fvars.get ⟨i, h⟩;
    decl ← getLocalDecl fvar.fvarId!;
    c?   ← isClassQuick decl.type;
    let addLocalInstance (className : Name) : MetaM α :=
      resettingTypeClassCache $
        adaptReader
          (fun (ctx : Context) => {
            localInstances := ctx.localInstances.push { className := className, fvar := fvar },
            .. ctx })
          (withNewLocalInstances (i+1) k);
    match c? with
    | LOption.none   => withNewLocalInstances (i+1) k
    | LOption.undef  => do
      c? ← isClassExpensive decl.type;
      match c? with
      | none   => withNewLocalInstances (i+1) k
      | some c => addLocalInstance c
    | LOption.some c => addLocalInstance c
  else
    k

/--
  `forallTelescopeAux whnf k lctx fvars j type`
  Remarks:
  - `lctx` is the `MetaM` local context exteded with the declaration for `fvars`.
  - `type` is the type we are computing the telescope for. It contains only
    dangling bound variables in the range `[j, fvars.size)`
  - when `type` is not a `forallE` nor it can't be reduced to one, we
    excute the continuation `k`. -/
@[specialize] private partial def forallTelescopeAuxAux {α}
    (whnf             : Expr → MetaM Expr)
    (isClassExpensive : Expr → MetaM (Option Name))
    (k                : Array Expr → Expr → MetaM α)
    : LocalContext → Array Expr → Nat → Expr → MetaM α
| lctx, fvars, j, Expr.forallE n bi d b => do
  let d := d.instantiateRevRange j fvars.size fvars;
  fvarId ← mkFreshId;
  let lctx := lctx.mkLocalDecl fvarId n d bi;
  let fvar := Expr.fvar fvarId;
  forallTelescopeAuxAux lctx (fvars.push fvar) j b
| lctx, fvars, j, type =>
  let type := type.instantiateRevRange j fvars.size fvars;
  adaptReader (fun (ctx : Context) => { lctx := lctx, .. ctx }) $
    withNewLocalInstances isClassExpensive fvars j $ do
      newType ← whnf type;
      if newType.isForall then
        forallTelescopeAuxAux lctx fvars fvars.size newType
      else
        k fvars type

/- We need this auxiliary definition because it depends on `isClassExpensive`,
   and `isClassExpensive` depends on it. -/
@[specialize] private def forallTelescopeAux {α}
    (whnf             : Expr → MetaM Expr)
    (isClassExpensive : Expr → MetaM (Option Name))
    (type : Expr) (k : Array Expr → Expr → MetaM α) : MetaM α :=
do newType ← whnf type;
   if newType.isForall then
     savingCache $ do
       lctx ← getLCtx;
       forallTelescopeAuxAux whnf isClassExpensive k lctx #[] 0 newType
   else do
     k #[] type

@[specialize] private partial def isClassExpensive
    (whnf : Expr → MetaM Expr)
    : Expr → MetaM (Option Name)
| type => byUnfoldingReducibleOnly $ -- when testing whether a type is a type class, we only unfold reducible constants.
  forallTelescopeAux whnf isClassExpensive type $ fun xs type => do
    match type.getAppFn with
    | Expr.const c _ => do
      env ← getEnv;
      pure $ if isClass env c then some c else none
    | _ => pure none

/--
  Given `type` of the form `forall xs, A`, execute `k xs A`.
  This combinator will declare local declarations, create free variables for them,
  execute `k` with updated local context, and make sure the cache is restored after executing `k`. -/
@[inline] def forallTelescope {α}
    (whnf : Expr → MetaM Expr)
    (type : Expr) (k : Array Expr → Expr → MetaM α) : MetaM α :=
forallTelescopeAux whnf (isClassExpensive whnf) type k

@[specialize] def isClass
    (whnf : Expr → MetaM Expr)
    (type : Expr) : MetaM (Option Name) :=
do c? ← isClassQuick type;
   match c? with
   | LOption.none   => pure none
   | LOption.some c => pure (some c)
   | LOption.undef  => isClassExpensive whnf type

/-- Similar to `forallTelescopeAuxAux` but for lambda and let expressions. -/
@[specialize] private partial def lambdaTelescopeAux {α}
    (whnf             : Expr → MetaM Expr)
    (k                : Array Expr → Expr → MetaM α)
    : LocalContext → Array Expr → Nat → Expr → MetaM α
| lctx, fvars, j, Expr.lam n bi d b => do
  let d := d.instantiateRevRange j fvars.size fvars;
  fvarId ← mkFreshId;
  let lctx := lctx.mkLocalDecl fvarId n d bi;
  let fvar := Expr.fvar fvarId;
  lambdaTelescopeAux lctx (fvars.push fvar) j b
| lctx, fvars, j, Expr.letE n t v b => do
  let t := t.instantiateRevRange j fvars.size fvars;
  let v := v.instantiateRevRange j fvars.size fvars;
  fvarId ← mkFreshId;
  let lctx := lctx.mkLetDecl fvarId n t v;
  let fvar := Expr.fvar fvarId;
  lambdaTelescopeAux lctx (fvars.push fvar) j b
| lctx, fvars, j, e =>
  let e := e.instantiateRevRange j fvars.size fvars;
  adaptReader (fun (ctx : Context) => { lctx := lctx, .. ctx }) $
    withNewLocalInstances (isClassExpensive whnf) fvars j $ do
      k fvars e

/-- Similar to `forallTelescope` but for lambda and let expressions. -/
@[specialize] private def lambdaTelescope {α}
    (whnf             : Expr → MetaM Expr)
    (e : Expr) (k : Array Expr → Expr → MetaM α) : MetaM α :=
savingCache $ do
  lctx ← getLCtx;
  lambdaTelescopeAux whnf k lctx #[] 0 e

@[specialize] private def getForallResultType
    (whnf      : Expr → MetaM Expr)
    (fType : Expr) (args : Array Expr) : MetaM Expr :=
do (j, fType) ← args.size.foldM
     (fun i (acc : Nat × Expr) =>
       let (j, type) := acc;
       match type with
       | Expr.forallE _ _ _ b => pure (j, b)
       | _ => do
         type ← whnf $ type.instantiateRevRange j i args;
         match type with
         | Expr.forallE _ _ _ b => pure (i, b)
         | _ => throwEx $ Exception.functionExpected fType args)
     (0, fType);
   pure $ fType.instantiateRevRange j args.size args

@[specialize] private def inferAppType
    (whnf      : Expr → MetaM Expr)
    (inferType : Expr → MetaM Expr)
    (f : Expr) (args : Array Expr) : MetaM Expr :=
do fType ← inferType f;
   getForallResultType whnf fType args

private def inferConstType (c : Name) (lvls : List Level) : MetaM Expr :=
do env ← getEnv;
   match env.find c with
   | some cinfo =>
     if cinfo.lparams.length == lvls.length then
       throwEx $ Exception.incorrectNumOfLevels c lvls
     else
       pure $ cinfo.instantiateTypeLevelParams lvls
   | none =>
     throwEx $ Exception.unknownConst c

@[specialize] private def inferProjType
    (whnf      : Expr → MetaM Expr)
    (inferType : Expr → MetaM Expr)
    (structName : Name) (idx : Nat) (e : Expr) : MetaM Expr :=
do let failed : Unit → MetaM Expr := fun _ => throwEx $ Exception.invalidProjection structName idx e;
   structType ← inferType e;
   structType ← whnf structType;
   env ← getEnv;
   matchConst env structType.getAppFn failed $ fun structInfo structLvls => do
     match structInfo with
     | ConstantInfo.inductInfo { nparams := n, ctors := [ctor], .. } =>
       let structParams := structType.getAppArgs;
       if n != structParams.size then failed ()
       else match env.find ctor with
         | none            => failed ()
         | some (ctorInfo) => do
           let ctorType := ctorInfo.instantiateTypeLevelParams structLvls;
           ctorType ← getForallResultType whnf ctorType structParams;
           ctorType ← idx.foldM
             (fun i ctorType => do
               ctorType ← whnf ctorType;
               match ctorType with
               | Expr.forallE _ _ _ body =>
                 if body.hasLooseBVars then
                   pure $ body.instantiate1 $ Expr.proj structName i e
                 else
                   pure body
               | _ => failed ())
             ctorType;
           ctorType ← whnf ctorType;
           match ctorType with
           | Expr.forallE _ _ d _ => pure d
           | _                    => failed ()
     | _ => failed ()

@[specialize] private def getLevel
    (whnf      : Expr → MetaM Expr)
    (inferType : Expr → MetaM Expr)
    (type : Expr) : MetaM Level :=
do typeType ← inferType type;
   typeType ← whnf type;
   match typeType with
   | Expr.sort lvl    => pure lvl
   | Expr.mvar mvarId =>
     condM (isReadOnlyOrSyntheticMVar mvarId)
       (throwEx $ Exception.typeExpected type)
       (do levelMVarId ← mkFreshId;
           let lvl := Level.mvar levelMVarId;
           assignExprMVar mvarId (Expr.sort lvl);
           pure lvl)
   | _ => throwEx $ Exception.typeExpected type

@[specialize] private def inferForallType
    (whnf      : Expr → MetaM Expr)
    (inferType : Expr → MetaM Expr)
    (e : Expr) : MetaM Expr :=
forallTelescope whnf e $ fun xs e => do
  type ← inferType e;
  lvl  ← getLevel whnf inferType type;
  lvl  ← xs.foldrM
    (fun x lvl => do
      xType    ← inferType x;
      xTypeLvl ← getLevel whnf inferType xType;
      pure $ Level.imax xTypeLvl lvl)
    lvl;
  pure $ Expr.sort lvl

/- Infer type of lambda and let expressions -/
@[specialize] private def inferLambdaType
    (whnf      : Expr → MetaM Expr)
    (inferType : Expr → MetaM Expr)
    (e : Expr) : MetaM Expr :=
lambdaTelescope whnf e $ fun xs e => do
  type ← inferType e;
  mkForall xs type

@[inline] private def withLocalDecl {α} (name : Name) (bi : BinderInfo) (type : Expr) (x : Expr → MetaM α) : MetaM α :=
savingCache $ do
  fvarId ← mkFreshId;
  adaptReader (fun (ctx : Context) => { lctx := ctx.lctx.mkLocalDecl fvarId name type bi, .. ctx }) $
    x (Expr.fvar fvarId)

private def inferMVarType (mvarId : Name) : MetaM Expr :=
do mctx ← getMCtx;
   match mctx.findDecl mvarId with
   | some d => pure d.type
   | none   => throwEx $ Exception.unknownMVar mvarId

private def inferFVarType (fvarId : Name) : MetaM Expr :=
do lctx ← getLCtx;
   match lctx.find fvarId with
   | some d => pure d.type
   | none   => throwEx $ Exception.unknownFVar fvarId

@[inline] private def checkInferTypeCache (e : Expr) (inferType : MetaM Expr) : MetaM Expr :=
do s ← get;
   match s.cache.inferType.find e with
   | some type => pure type
   | none => do
     type ← inferType;
     modify $ fun s => { cache := { inferType := s.cache.inferType.insert e type, .. s.cache }, .. s };
     pure type

@[specialize] private partial def inferTypeAux
    (whnf      : Expr → MetaM Expr)
    : Expr → MetaM Expr
| Expr.const c lvls        => inferConstType c lvls
| e@(Expr.proj n i s)      => checkInferTypeCache e (inferProjType whnf inferTypeAux n i s)
| e@(Expr.app f _)         => checkInferTypeCache e (inferAppType whnf inferTypeAux f e.getAppArgs)
| Expr.mvar mvarId         => inferMVarType mvarId
| Expr.fvar fvarId         => inferFVarType fvarId
| Expr.bvar _              => unreachable!
| Expr.mdata _ e           => inferTypeAux e
| Expr.lit v               => pure v.type
| Expr.sort lvl            => pure $ Expr.sort (Level.succ lvl)
| e@(Expr.forallE _ _ _ _) => checkInferTypeCache e (inferForallType whnf inferTypeAux e)
| e@(Expr.lam _ _ _ _)     => checkInferTypeCache e (inferLambdaType whnf inferTypeAux e)
| e@(Expr.letE _ _ _ _)    => checkInferTypeCache e (inferLambdaType whnf inferTypeAux e)

#exit

@[inline] private def liftStateMCtx {α} (x : StateM σ α) : TypeUtilM σ ϕ α :=
fun _ s =>
  let (a, mctx) := x.run s.mctx;
  EStateM.Result.ok a { mctx := mctx, .. s }

export AbstractMetavarContext (hasAssignableLevelMVar isReadOnlyLevelMVar auxMVarSupport getExprAssignment)

/- ===========================
   inferType
   =========================== -/
@[specialize] private def inferTypeAux
    [AbstractMetavarContext σ]
    [AbstractTypeUtilCache ϕ]
    (whnf : Expr → TypeUtilM σ ϕ Expr)
    (inferType : Expr → TypeUtilM σ ϕ Expr)
    (isDefEq : Expr → Expr → TypeUtilM σ ϕ Bool)
    : Expr → TypeUtilM σ ϕ Expr :=
fun _ => throw $ TypeUtilException.other "not implemented yet"

/- ===========================
   isDefEq for universe levels
   =========================== -/

private def instantiateLevelMVars [AbstractMetavarContext σ] (lvl : Level) : TypeUtilM σ ϕ Level :=
liftStateMCtx $ AbstractMetavarContext.instantiateLevelMVars lvl

private def assignLevel [AbstractMetavarContext σ] (mvarId : Name) (lvl : Level) : TypeUtilM σ ϕ Unit :=
modify $ fun s => { mctx := AbstractMetavarContext.assignLevel s.mctx mvarId lvl, .. s }

private def mkFreshLevelMVar [AbstractMetavarContext σ] : TypeUtilM σ ϕ Level :=
modifyGet $ fun s => (Level.mvar s.ngen.curr, { ngen := s.ngen.next, .. s })

private def strictOccursMaxAux (lvl : Level) : Level → Bool
| Level.max u v => strictOccursMaxAux u || strictOccursMaxAux v
| u             => u != lvl && lvl.occurs u

/--
  Return true iff `lvl` occurs in `max u_1 ... u_n` and `lvl != u_i` for all `i in [1, n]`.
  That is, `lvl` is a proper level subterm of some `u_i`. -/
private def strictOccursMax (lvl : Level) : Level → Bool
| Level.max u v => strictOccursMaxAux lvl u || strictOccursMaxAux lvl v
| _             => false

/-- `mkMaxArgsDiff mvarId (max u_1 ... (mvar mvarId) ... u_n) v` => `max v u_1 ... u_n` -/
private def mkMaxArgsDiff (mvarId : Name) : Level → Level → Level
| Level.max u v,     acc => mkMaxArgsDiff v $ mkMaxArgsDiff u acc
| l@(Level.mvar id), acc => if id != mvarId then Level.max acc l else acc
| l,                 acc => Level.max acc l

/--
  Solve `?m =?= max ?m v` by creating a fresh metavariable `?n`
  and assigning `?m := max ?n v` -/
private def solveSelfMax [AbstractMetavarContext σ] (mvarId : Name) (v : Level) : TypeUtilM σ ϕ Unit :=
do n ← mkFreshLevelMVar;
   let lhs := mkMaxArgsDiff mvarId v n;
   assignLevel mvarId lhs

private def postponeIsLevelDefEq (lhs : Level) (updateLhs : Bool) (rhs : Level) (updateRhs : Bool) : TypeUtilM σ ϕ Unit :=
modify $ fun s => { postponed := s.postponed.push { lhs := lhs, updateLhs := updateLhs, rhs := rhs, updateRhs := updateRhs }, .. s }

private partial def isLevelDefEqAux [AbstractMetavarContext σ] (updateLhs updateRhs : Bool) : Level → Level → TypeUtilM σ ϕ Bool
| Level.succ lhs, Level.succ rhs => isLevelDefEqAux lhs rhs
| lhs, rhs =>
  if lhs == rhs then
    pure true
  else do
    trace! `type_context.level_is_def_eq (lhs ++ " =?= " ++ rhs);
    lhs' ← instantiateLevelMVars lhs;
    let lhs' := lhs'.normalize;
    rhs' ← instantiateLevelMVars rhs;
    let rhs' := rhs'.normalize;
    if lhs != lhs' || rhs != rhs' then
      isLevelDefEqAux lhs' rhs'
    else do
      mctx ← getMCtx;
      if (!updateLhs || !hasAssignableLevelMVar mctx lhs) &&
         (!updateRhs || !hasAssignableLevelMVar mctx rhs) then
        pure false
      else if updateLhs && lhs.isMVar && !isReadOnlyLevelMVar mctx lhs.mvarId! && !lhs.occurs rhs then do
        assignLevel lhs.mvarId! rhs;
        pure true
      else if auxMVarSupport σ && updateLhs && lhs.isMVar && !isReadOnlyLevelMVar mctx lhs.mvarId! && !strictOccursMax lhs rhs then do
        solveSelfMax lhs.mvarId! rhs;
        pure true
      else if updateRhs && rhs.isMVar && !isReadOnlyLevelMVar mctx rhs.mvarId! && !rhs.occurs lhs then do
        assignLevel rhs.mvarId! lhs;
        pure true
      else if auxMVarSupport σ && updateRhs && rhs.isMVar && !isReadOnlyLevelMVar mctx rhs.mvarId! && !strictOccursMax rhs lhs then do
        solveSelfMax rhs.mvarId! lhs;
        pure true
      else if lhs.isMVar || rhs.isMVar then
        pure false
      else
        if lhs.isSucc || rhs.isSucc then
          match lhs.dec, rhs.dec with
          | some lhs', some rhs' => isLevelDefEqAux lhs' rhs'
          | _,         _         => do
            postponeIsLevelDefEq lhs updateLhs rhs updateRhs;
            pure true
        else do
          postponeIsLevelDefEq lhs updateLhs rhs updateRhs;
          pure true

private def getNumPostponed : TypeUtilM σ ϕ Nat :=
do s ← get;
   pure s.postponed.size

private def getResetPostponed : TypeUtilM σ ϕ (Array PostponedEntry) :=
do s ← get;
   let ps := s.postponed;
   modify $ fun s => { postponed := #[], .. s };
   pure ps

private def processPostponedStep [AbstractMetavarContext σ] : TypeUtilM σ ϕ Bool :=
traceCtx `type_context.level_is_def_eq.postponed_step $ do
  ps ← getResetPostponed;
  ps.foldlM
    (fun (r : Bool) (p : PostponedEntry) =>
      if r then
        isLevelDefEqAux p.updateLhs p.updateRhs p.lhs p.rhs
      else
        pure false)
    true

private partial def processPostponedAux [AbstractMetavarContext σ] : Bool → TypeUtilM σ ϕ Bool
| mayPostpone => do
  numPostponed ← getNumPostponed;
  if numPostponed == 0 then
    pure true
  else do
    trace! `type_context.level_is_def_eq ("processing #" ++ toString numPostponed ++ " postponed is-def-eq level constraints");
    r ← processPostponedStep;
    if !r then
      pure r
    else do
      numPostponed' ← getNumPostponed;
      if numPostponed' == 0 then
        pure true
      else if numPostponed' < numPostponed then
        processPostponedAux mayPostpone
      else do
        trace! `type_context.level_is_def_eq ("no progress solving pending is-def-eq level constraints");
        pure mayPostpone

private def processPostponed [AbstractMetavarContext σ] (mayPostpone : Bool) : TypeUtilM σ ϕ Bool :=
do numPostponed ← getNumPostponed;
   if numPostponed == 0 then pure true
   else traceCtx `type_context.level_is_def_eq.postponed $ processPostponedAux mayPostpone

@[inline] private def restoreIfFalse (x : TypeUtilM σ ϕ Bool) : TypeUtilM σ ϕ Bool :=
do s ← get;
   let mctx      := s.mctx;
   let postponed := s.postponed;
   catch
     (do b ← x;
       unless b $ modify $ fun s => { mctx := mctx, postponed := postponed, .. s };
       pure b)
     (fun e => do
       modify $ fun s => { mctx := mctx, postponed := postponed, .. s };
       throw e)

/- ===========================
   isDefEq for Expr
   =========================== -/
@[specialize] private def isDefEqAux
    [AbstractMetavarContext σ]
    [AbstractTypeUtilCache ϕ]
    (whnf : Expr → TypeUtilM σ ϕ Expr)
    (inferType : Expr → TypeUtilM σ ϕ Expr)
    (isDefEq : Expr → Expr → TypeUtilM σ ϕ Bool)
    : Expr → Expr → TypeUtilM σ ϕ Bool :=
fun _ _ => throw $ TypeUtilException.other "not implemented yet"

/- Public interface -/

def isLevelDefEq [AbstractMetavarContext σ] (u v : Level) (mayPostpone : Bool := false) : TypeUtilM σ ϕ Bool :=
restoreIfFalse $ do
  r ← isLevelDefEqAux true true u v;
  if !r then pure false
  else processPostponed mayPostpone

/- =========================================== -/
/- BIG HACK until we add `mutual` keyword back -/
/- =========================================== -/
inductive TypeUtilOp
| whnfOp | inferTypeOp | isDefEqOp
open TypeUtilOp
private def exprToBool : Expr → Bool
| Expr.sort Level.zero => false
| _                    => true
private def boolToExpr : Bool → Expr
| false => Expr.sort Level.zero
| true  => Expr.bvar 0

private partial def auxFixpoint [AbstractMetavarContext σ] [AbstractTypeUtilCache ϕ] : TypeUtilOp → Expr → Expr → TypeUtilM σ ϕ Expr
| op, e₁, e₂ =>
  let whnf      := fun e => auxFixpoint whnfOp e e;
  let inferType := fun e => auxFixpoint inferTypeOp e e;
  let isDefEq   := fun e₁ e₂ => exprToBool <$> auxFixpoint isDefEqOp e₁ e₂;
  match op with
  | whnfOp      => whnfAux whnf inferType isDefEq e₁
  | inferTypeOp => inferTypeAux whnf inferType isDefEq e₁
  | isDefEqOp   => boolToExpr <$> isDefEqAux whnf inferType isDefEq e₁ e₂

def whnf [AbstractMetavarContext σ] [AbstractTypeUtilCache ϕ] (e : Expr) : TypeUtilM σ ϕ Expr :=
auxFixpoint whnfOp e e

def inferType [AbstractMetavarContext σ] [AbstractTypeUtilCache ϕ] (e : Expr) : TypeUtilM σ ϕ Expr :=
auxFixpoint inferTypeOp e e

def isDefEq [AbstractMetavarContext σ] [AbstractTypeUtilCache ϕ] (e₁ e₂ : Expr) : TypeUtilM σ ϕ Bool :=
exprToBool <$> auxFixpoint isDefEqOp e₁ e₂
/- =========================================== -/
/-          END OF BIG HACK                    -/
/- =========================================== -/

end TypeUtil

inductive TypeUtilNoCache
| mk

instance typeContextNoCacheIsAbstractTCCache : AbstractTypeUtilCache TypeUtilNoCache :=
{ getWHNF := fun _ _ _ => none,
  setWHNF := fun s _ _ _ => s }

end Lean
