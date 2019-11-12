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
import Init.Lean.Class
import Init.Lean.ReducibilityAttrs
import Init.Lean.Meta.Exception

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

structure ParamInfo :=
(implicit     : Bool      := false)
(instImplicit : Bool      := false)
(prop         : Bool      := false)
(hasFwdDeps   : Bool      := false)
(backDeps     : Array Nat := #[])

structure FunInfo :=
(paramInfo  : Array ParamInfo := #[])
(resultDeps : Array Nat       := #[])

structure InfoCacheKey :=
(transparency : TransparencyMode)
(expr         : Expr)
(nargs?       : Option Nat)

namespace InfoCacheKey
instance : Inhabited InfoCacheKey := ⟨⟨arbitrary _, arbitrary _, arbitrary _⟩⟩
instance : Hashable InfoCacheKey :=
⟨fun ⟨transparency, expr, nargs⟩ => mixHash (hash transparency) $ mixHash (hash expr) (hash nargs)⟩
instance : HasBeq InfoCacheKey :=
⟨fun ⟨t₁, e₁, n₁⟩ ⟨t₂, e₂, n₂⟩ => t₁ == t₂ && n₁ == n₂ && e₁ == e₂⟩
end InfoCacheKey

structure Cache :=
(inferType : PersistentExprStructMap Expr := {})
(funInfo   : PersistentHashMap InfoCacheKey FunInfo := {})

structure Context :=
(config         : Config         := {})
(lctx           : LocalContext   := {})
(localInstances : LocalInstances := #[])

structure PostponedEntry :=
(lhs       : Level)
(rhs       : Level)

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

@[inline] def getLCtx : MetaM LocalContext :=
do ctx ← read; pure ctx.lctx

@[inline] def getMCtx : MetaM MetavarContext :=
do s ← get; pure s.mctx

@[inline] def getEnv : MetaM Environment :=
do s ← get; pure s.env

@[inline] def throwEx {α} (f : ExceptionContext → Exception) : MetaM α :=
do ctx ← read;
   s ← get;
   throw (f {env := s.env, mctx := s.mctx, lctx := ctx.lctx })

@[inline] def throwBug {α} (b : Bug) : MetaM α :=
throwEx $ Exception.bug b

/-- Execute `x` only in debugging mode. -/
@[inline] private def whenDebugging {α} (x : MetaM α) : MetaM Unit :=
do ctx ← read;
   when ctx.config.debug (do x; pure ())

def mkFreshId : MetaM Name :=
do s ← get;
   let id := s.ngen.curr;
   modify $ fun s => { ngen := s.ngen.next, .. s };
   pure id

@[inline] private def reduceAll? : MetaM Bool :=
do ctx ← read; pure $ ctx.config.transparency == TransparencyMode.all

@[inline] private def reduceReducibleOnly? : MetaM Bool :=
do ctx ← read; pure $ ctx.config.transparency == TransparencyMode.reducible

@[inline] def getTransparency : MetaM TransparencyMode :=
do ctx ← read; pure $ ctx.config.transparency

@[inline] private def getOptions : MetaM Options :=
do ctx ← read; pure ctx.config.opts

-- Remark: wanted to use `private`, but in C++ parser, `private` declarations do not shadow outer public ones.
-- TODO: fix this bug
@[inline] def isReducible (constName : Name) : MetaM Bool :=
do env ← getEnv; pure $ isReducible env constName

/-- While executing `x`, ensure the given transparency mode is used. -/
@[inline] def usingTransparency {α} (mode : TransparencyMode) (x : MetaM α) : MetaM α :=
adaptReader
  (fun (ctx : Context) => { config := { transparency := mode, .. ctx.config }, .. ctx })
  x

def isReadOnlyOrSyntheticExprMVar (mvarId : Name) : MetaM Bool :=
do mctx ← getMCtx;
   match mctx.findDecl mvarId with
   | some d => pure $ d.synthetic || d.depth != mctx.depth
   | _      => throwEx $ Exception.unknownExprMVar mvarId

def isReadOnlyLevelMVar (mvarId : Name) : MetaM Bool :=
do mctx ← getMCtx;
   match mctx.findLevelDepth mvarId with
   | some depth => pure $ depth != mctx.depth
   | _          => throwEx $ Exception.unknownLevelMVar mvarId

@[inline] private def isExprAssigned (mvarId : Name) : MetaM Bool :=
do mctx ← getMCtx;
   pure $ mctx.isExprAssigned mvarId

@[inline] def getExprMVarAssignment (mvarId : Name) : MetaM (Option Expr) :=
do mctx ← getMCtx; pure (mctx.getExprAssignment mvarId)

def assignExprMVar (mvarId : Name) (val : Expr) : MetaM Unit :=
do whenDebugging $ whenM (isExprAssigned mvarId) $ throwBug $ Bug.overwritingExprMVar mvarId;
   modify $ fun s => { mctx := s.mctx.assignExpr mvarId val, .. s }

def dbgTrace {α} [HasToString α] (a : α) : MetaM Unit :=
_root_.dbgTrace (toString a) $ fun _ => pure ()

@[inline] private def getTraceState : MetaM TraceState :=
do s ← get; pure s.traceState

instance tracer : SimpleMonadTracerAdapter MetaM :=
{ getOptions       := getOptions,
  getTraceState    := getTraceState,
  modifyTraceState := fun f => modify $ fun s => { traceState := f s.traceState, .. s } }

def getConstAux (constName : Name) (exception? : Bool) : MetaM (Option ConstantInfo) :=
do env ← getEnv;
   match env.find constName with
   | some (info@(ConstantInfo.thmInfo _)) =>
     condM reduceAll? (pure (some info)) (pure none)
   | some info                            =>
     condM reduceReducibleOnly?
       (condM (isReducible constName) (pure (some info)) (pure none))
       (pure (some info))
   | none                                 =>
     if exception? then throwEx $ Exception.unknownConst constName
     else pure none

@[inline] def getConst (constName : Name) : MetaM (Option ConstantInfo) :=
getConstAux constName true

@[inline] def getConstNoEx (constName : Name) : MetaM (Option ConstantInfo) :=
getConstAux constName false

def getLocalDecl (fvarId : Name) : MetaM LocalDecl :=
do lctx ← getLCtx;
   match lctx.find fvarId with
   | some d => pure d
   | none   => throwEx $ Exception.unknownFVar fvarId

def instantiateMVars (e : Expr) : MetaM Expr :=
if e.hasMVar then
  modifyGet $ fun s =>
    let (e, mctx) := s.mctx.instantiateMVars e;
    (e, { mctx := mctx, .. s })
else
  pure e

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
@[inline] def savingCache {α} (x : MetaM α) : MetaM α :=
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
  val? ← getExprMVarAssignment mvarId;
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
  if `reducing? == true`, the function executes `k #[(x : Nat) (s : Int)] Bool`.
  if `reducing? == false`, the function executes `k #[(x : Nat)] (StateM Int Bool)`

  if `maxFVars?` is `some max`, then we interrupt the telescope construction
  when `fvars.size == max`
-/
@[specialize] private partial def forallTelescopeReducingAuxAux {α}
    (whnf             : Expr → MetaM Expr)
    (isClassExpensive : Expr → MetaM (Option Name))
    (reducing?        : Bool) (maxFVars? : Option Nat)
    (k                : Array Expr → Expr → MetaM α)
    : LocalContext → Array Expr → Nat → Expr → MetaM α
| lctx, fvars, j, Expr.forallE n bi d b => do
  let d     := d.instantiateRevRange j fvars.size fvars;
  fvarId ← mkFreshId;
  let lctx  := lctx.mkLocalDecl fvarId n d bi;
  let fvar  := Expr.fvar fvarId;
  let fvars := fvars.push fvar;
  match maxFVars? with
  | none          => forallTelescopeReducingAuxAux lctx fvars j b
  | some maxFVars =>
    if fvars.size < maxFVars then
      forallTelescopeReducingAuxAux lctx fvars j b
    else
      let type := b.instantiateRevRange j fvars.size fvars;
      adaptReader (fun (ctx : Context) => { lctx := lctx, .. ctx }) $
        withNewLocalInstances isClassExpensive fvars j $
          k fvars type
| lctx, fvars, j, type =>
  let type := type.instantiateRevRange j fvars.size fvars;
  adaptReader (fun (ctx : Context) => { lctx := lctx, .. ctx }) $
    withNewLocalInstances isClassExpensive fvars j $
      if reducing? then do
        newType ← whnf type;
        if newType.isForall then
          forallTelescopeReducingAuxAux lctx fvars fvars.size newType
        else
          k fvars type
      else
        k fvars type

/- We need this auxiliary definition because it depends on `isClassExpensive`,
   and `isClassExpensive` depends on it. -/
@[specialize] private def forallTelescopeReducingAux {α}
    (whnf             : Expr → MetaM Expr)
    (isClassExpensive : Expr → MetaM (Option Name))
    (type : Expr) (maxFVars? : Option Nat) (k : Array Expr → Expr → MetaM α) : MetaM α :=
do newType ← whnf type;
   if newType.isForall then
     savingCache $ do
       lctx ← getLCtx;
       forallTelescopeReducingAuxAux whnf isClassExpensive true maxFVars? k lctx #[] 0 newType
   else
     k #[] type

@[specialize] private partial def isClassExpensive
    (whnf : Expr → MetaM Expr)
    : Expr → MetaM (Option Name)
| type => usingTransparency TransparencyMode.reducible $ -- when testing whether a type is a type class, we only unfold reducible constants.
  forallTelescopeReducingAux whnf isClassExpensive type none $ fun xs type => do
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
savingCache $ do
  lctx ← getLCtx;
  forallTelescopeReducingAuxAux whnf (isClassExpensive whnf) false none k lctx #[] 0 type

/--
  Similar to `forallTelescope`, but given `type` of the form `forall xs, A`,
  it reduces `A` and continues bulding the telescope if it is a `forall`. -/
@[specialize] def forallTelescopeReducing {α}
    (whnf : Expr → MetaM Expr)
    (type : Expr) (k : Array Expr → Expr → MetaM α) : MetaM α :=
forallTelescopeReducingAux whnf (isClassExpensive whnf) type none k

/--
  Similar to `forallTelescopeReducing`, stops constructing the telescope when
  it reaches size `maxFVars`. -/
@[specialize] def forallBoundedTelescope {α}
    (whnf : Expr → MetaM Expr)
    (type : Expr) (maxFVars? : Option Nat) (k : Array Expr → Expr → MetaM α) : MetaM α :=
forallTelescopeReducingAux whnf (isClassExpensive whnf) type maxFVars? k

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
@[specialize] def lambdaTelescope {α}
    (whnf             : Expr → MetaM Expr)
    (e : Expr) (k : Array Expr → Expr → MetaM α) : MetaM α :=
savingCache $ do
  lctx ← getLCtx;
  lambdaTelescopeAux whnf k lctx #[] 0 e

@[inline] def liftStateMCtx {α} (x : StateM MetavarContext α) : MetaM α :=
fun _ s =>
  let (a, mctx) := x.run s.mctx;
  EStateM.Result.ok a { mctx := mctx, .. s }

def instantiateLevelMVars (lvl : Level) : MetaM Level :=
liftStateMCtx $ MetavarContext.instantiateLevelMVars lvl

def assignLevelMVar (mvarId : Name) (lvl : Level) : MetaM Unit :=
modify $ fun s => { mctx := MetavarContext.assignLevel s.mctx mvarId lvl, .. s }

def mkFreshLevelMVarId : MetaM Name :=
do mvarId ← mkFreshId;
   modify $ fun s => { mctx := s.mctx.addLevelMVarDecl mvarId, .. s };
   pure mvarId

@[inline] def usingDefault (whnf : Expr → MetaM Expr) : Expr → MetaM Expr :=
fun e => usingTransparency TransparencyMode.default $ whnf e

end Meta
end Lean
