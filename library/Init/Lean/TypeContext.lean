/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Control.Reader
import Init.Lean.NameGenerator
import Init.Lean.Environment
import Init.Lean.LocalContext
import Init.Lean.Trace

namespace Lean
inductive TransparencyMode
| All | Semireducible | Instances | Reducible | None

structure LocalInstance :=
(className : Name)
(fvar      : Expr)

abbrev LocalInstances := Array LocalInstance

structure UnifierOptions :=
(foApprox           : Bool := false)
(ctxApprox          : Bool := false)
(quasiPatternApprox : Bool := false)

structure TCOptions :=
(opts           : Options          := {})
(unifierConfig  : UnifierOptions   := {})
(transparency   : TransparencyMode := TransparencyMode.Semireducible)
(smartUnfolding : Bool             := true)
(useZeta        : Bool             := true)

/- We can `TypeContext` functions with different implementations of
   metavariable contexts.  For elaboration and tactic framework, we
   use `MetavarContext`.  During type class resolution and simplifier,
   we use temporary metavariables which are cheaper to create and
   dispose. Moreover, given a particular task using temporary
   metavariables (e.g., matching the left-hand side of an equation),
   we assume all metavariables share the same local context.
   If `sharedContext == false`, then support for "delayed assignments" is
   required. -/
class AbstractMetavarContext (σ : Type) :=
(empty                : σ)
(isLevelMVar {}       : Level → Bool)
(getLevelAssignment   (mctx : σ) (mvarId : Name) : Option Level)
(assignLevel          (mctx : σ) (mvarId : Name) (val : Level) : σ)
(isExprMVar {}        : Expr → Bool)
(getExprAssignment    (mctx : σ) (mvarId : Name) : Option Expr)
(assignExpr           (mctx : σ) (mvarId : Name) (val : Expr) : σ)
(getExprMVarLCtx      (mctx : σ) (mvarId : Name) : Option LocalContext)
(getExprMVarType      (mctx : σ) (mvarId : Name) : Option Expr)
(sharedContext        : Bool)
(assignDelayed        (mctx : σ) (mvarId : Name) (lctx : LocalContext) (fvars : Array Expr) (val : Expr) : σ)
(getDelayedAssignment (mctx : σ) (mvarId : Name) : Option DelayedMVarAssignment)
(eraseDelayed         (mctx : σ) (mvarId : Name) : σ)

/- Abstract cache interfact for `TypeContext` functions.
   TODO: add missing methods. -/
class AbstractTCCache (ϕ : Type) :=
(getWHNF : ϕ → TransparencyMode → Expr → Option Expr)
(setWHNF : ϕ → TransparencyMode → Expr → Expr → ϕ)

-- TODO: add special cases
inductive TCException
| other : String → TCException

structure TCContext :=
(env            : Environment)
(lctx           : LocalContext)
(localInstances : LocalInstances)
(config         : TCOptions := {})

structure TCState (σ ϕ : Type) :=
(mctx           : σ)
(cache          : ϕ)
(ngen           : NameGenerator)
(traceState     : TraceState)
(usedAssignment : Bool := false)
(postponed      : Array (Level × Level) := #[])

instance TCState.backtrackable {σ ϕ} : EState.Backtrackable σ (TCState σ ϕ) :=
{ save    := fun s => s.mctx,
  restore := fun s mctx => { mctx := mctx, .. s } }

/-- Abstract Type Context Monad -/
abbrev ATCM (σ ϕ : Type) := ReaderT TCContext (EState TCException (TCState σ ϕ))

namespace AbstractTypeContext

variables {σ ϕ : Type}

@[inline] def isLevelAssigned {σ} [AbstractMetavarContext σ] (mctx : σ) (mvarId : Name) : Bool :=
(AbstractMetavarContext.getLevelAssignment mctx mvarId).isSome

@[inline] def isExprAssigned {σ} [AbstractMetavarContext σ] (mctx : σ) (mvarId : Name) : Bool :=
(AbstractMetavarContext.getExprAssignment mctx mvarId).isSome

def hasAssignedLevelMVar {σ} [AbstractMetavarContext σ] (mctx : σ) : Level → Bool
| Level.succ lvl       => lvl.hasMVar && hasAssignedLevelMVar lvl
| Level.max lvl₁ lvl₂  => (lvl₁.hasMVar && hasAssignedLevelMVar lvl₁) || (lvl₂.hasMVar && hasAssignedLevelMVar lvl₂)
| Level.imax lvl₁ lvl₂ => (lvl₁.hasMVar && hasAssignedLevelMVar lvl₁) || (lvl₂.hasMVar && hasAssignedLevelMVar lvl₂)
| Level.mvar mvarId    => isLevelAssigned mctx mvarId
| Level.zero           => false
| Level.param _        => false

/-- Return `true` iff expression contains assigned (level/expr) metavariables -/
def hasAssignedMVar {σ} [AbstractMetavarContext σ] (mctx : σ) : Expr → Bool
| Expr.const _ lvls    => lvls.any (hasAssignedLevelMVar mctx)
| Expr.sort lvl        => hasAssignedLevelMVar mctx lvl
| Expr.app f a         => (f.hasMVar && hasAssignedMVar f) || (a.hasMVar && hasAssignedMVar a)
| Expr.letE _ t v b    => (t.hasMVar && hasAssignedMVar t) || (v.hasMVar && hasAssignedMVar v) || (b.hasMVar && hasAssignedMVar b)
| Expr.forallE _ _ d b => (d.hasMVar && hasAssignedMVar d) || (b.hasMVar && hasAssignedMVar b)
| Expr.lam _ _ d b     => (d.hasMVar && hasAssignedMVar d) || (b.hasMVar && hasAssignedMVar b)
| Expr.fvar _          => false
| Expr.bvar _          => false
| Expr.lit _           => false
| Expr.mdata _ e       => e.hasMVar && hasAssignedMVar e
| Expr.proj _ _ e      => e.hasMVar && hasAssignedMVar e
| Expr.mvar mvarId     => isExprAssigned mctx mvarId

partial def instantiateLevelMVars {σ} [AbstractMetavarContext σ] : Level → State σ Level
| lvl@(Level.succ lvl₁)       => do lvl₁ ← instantiateLevelMVars lvl₁; pure (Level.updateSucc! lvl lvl₁)
| lvl@(Level.max lvl₁ lvl₂)   => do lvl₁ ← instantiateLevelMVars lvl₁; lvl₂ ← instantiateLevelMVars lvl₂; pure (Level.updateMax! lvl lvl₁ lvl₂)
| lvl@(Level.imax lvl₁ lvl₂)  => do lvl₁ ← instantiateLevelMVars lvl₁; lvl₂ ← instantiateLevelMVars lvl₂; pure (Level.updateIMax! lvl lvl₁ lvl₂)
| lvl@(Level.mvar mvarId) => do
  mctx ← get;
  match AbstractMetavarContext.getLevelAssignment mctx mvarId with
  | some newLvl =>
    if !newLvl.hasMVar then pure newLvl
    else do
      newLvl' ← instantiateLevelMVars newLvl;
      modify $ fun mctx => AbstractMetavarContext.assignLevel mctx mvarId newLvl';
      pure newLvl'
  | none        => pure lvl
| lvl => pure lvl

namespace InstantiateExprMVars
/-- Auxiliary structure for instantiating metavariables in `Expr`s. -/
structure InstState (σ : Type) :=
(mctx  : σ)
(cache : ExprMap Expr := {})

abbrev M (σ : Type) := State (InstState σ)

@[inline] def instantiateLevelMVars {σ} [AbstractMetavarContext σ] (lvl : Level) : M σ Level :=
adaptState
  (fun (s : InstState σ) => (s.mctx, { mctx := AbstractMetavarContext.empty σ, .. s }))
  (fun (mctx : σ) (s : InstState σ) => { mctx := mctx, .. s })
  (AbstractTypeContext.instantiateLevelMVars lvl : State σ Level)

@[inline] def checkCache {σ} (e : Expr) (f : Expr → M σ Expr) : M σ Expr :=
do s ← get;
   match s.cache.find e with
   | some r => pure r
   | none => do
     r ← f e;
     modify $ fun s => { cache := s.cache.insert e r, .. s };
     pure r

@[inline] def visit {σ} (f : Expr → M σ Expr) (e : Expr) : M σ Expr :=
if !e.hasMVar then pure e else checkCache e f

@[inline] def getMCtx {σ} : M σ σ :=
do s ← get; pure s.mctx

/--
  Auxiliary function for `instantiateDelayed`.
  `instantiateDelayed main lctx fvars i body` is used to create `fun fvars[0, i) => body`.
  It fails if one of variable declarations in `fvars` still contains unassigned metavariables.

  Pre: all expressions in `fvars` are `Expr.fvar`, and `lctx` contains their declarations. -/
@[specialize] def instantiateDelayedAux {σ} [AbstractMetavarContext σ] (main : Expr → M σ Expr) (lctx : LocalContext) (fvars : Array Expr) : Nat → Expr → M σ (Option Expr)
| 0,   b => pure b
| i+1, b => do
  let fvar := fvars.get! i;
  match lctx.findFVar fvar with
  | none => panic! "unknown local declaration"
  | some (LocalDecl.cdecl _ _ n ty bi)  => do
    ty ← visit main ty;
    if ty.hasMVar then pure none
    else instantiateDelayedAux i (Expr.lam n bi (ty.abstractRange i fvars) b)
  | some (LocalDecl.ldecl _ _ n ty val) => do
    ty  ← visit main ty;
    if ty.hasMVar then pure none
    else do
      val ← visit main val;
      if val.hasMVar then pure none
      else
        let ty  := ty.abstractRange i fvars;
        let val := val.abstractRange i fvars;
        instantiateDelayedAux i (Expr.letE n ty val b)

/-- Try to instantiate a delayed assignment. Return `none` (i.e., fail) if assignment still contains variables. -/
@[inline] def instantiateDelayed {σ} [AbstractMetavarContext σ] (main : Expr → M σ Expr) (mvarId : Name) : DelayedMVarAssignment → M σ (Option Expr)
| { lctx := lctx, fvars := fvars, val := val } => do
  newVal ← visit main val;
  let fail : M σ (Option Expr) := do {
     /- Join point for updating delayed assignment and failing -/
     modify $ fun s => { mctx := AbstractMetavarContext.assignDelayed s.mctx mvarId lctx fvars newVal, .. s };
     pure none
  };
  if newVal.hasMVar then fail
  else do
    /- Create `fun fvars => newVal`.
       It fails if there is a one of the variable declarations in `fvars` still contain metavariables. -/
    newE ← instantiateDelayedAux main lctx fvars fvars.size (newVal.abstract fvars);
    match newE with
    | none      => fail
    | some newE => do
      /- Succeeded. Thus, replace delayed assignment with a regular assignment. -/
      modify $ fun s =>
        let mctx := AbstractMetavarContext.eraseDelayed s.mctx mvarId;
        { mctx := AbstractMetavarContext.assignExpr mctx mvarId newE, .. s };
      pure (some newE)

/-- instantiateExprMVars main function -/
partial def main {σ} [AbstractMetavarContext σ] : Expr → M σ Expr
| e@(Expr.proj _ _ s)      => do s ← visit main s; pure (e.updateProj! s)
| e@(Expr.forallE _ _ d b) => do d ← visit main d; b ← visit main b; pure (e.updateForallE! d b)
| e@(Expr.lam _ _ d b)     => do d ← visit main d; b ← visit main b; pure (e.updateLambdaE! d b)
| e@(Expr.letE _ t v b)    => do t ← visit main t; v ← visit main v; b ← visit main b; pure (e.updateLet! t v b)
| e@(Expr.const _ lvls)    => do lvls ← lvls.mmap instantiateLevelMVars; pure (e.updateConst! lvls)
| e@(Expr.sort lvl)        => do lvl ← instantiateLevelMVars lvl; pure (e.updateSort! lvl)
| e@(Expr.mdata _ b)       => do b ← visit main b; pure (e.updateMData! b)
| e@(Expr.app _ _)         => e.withAppRev $ fun f revArgs => do
  let wasMVar := f.isMVar;
  f ← visit main f;
  if wasMVar && f.isLambda then
    -- Some of the arguments in revArgs are irrelevant after we beta reduce.
    visit main (f.betaRev revArgs)
  else do
    revArgs ← revArgs.mmap (visit main);
    pure (mkAppRev f revArgs)
| e@(Expr.mvar mvarId)     => checkCache e $ fun e => do
  mctx ← getMCtx;
  match AbstractMetavarContext.getExprAssignment mctx mvarId with
  | some newE => do
    newE' ← visit main newE;
    modify $ fun s => { mctx := AbstractMetavarContext.assignExpr s.mctx mvarId newE', .. s };
    pure newE'
  | none =>
    /- A delayed assignment can be transformed into a regular assignment
       as soon as all metavariables occurring in the assigned value have
       been assigned. -/
    match AbstractMetavarContext.getDelayedAssignment mctx mvarId with
    | some d => do
       newE ← instantiateDelayed main mvarId d;
       pure $ newE.getD e
    | none   => pure e
| e => pure e

end InstantiateExprMVars

def instantiateExprMVars {σ} [AbstractMetavarContext σ] (e : Expr) : State σ Expr :=
if !e.hasMVar then pure e
else
  adaptState'
    (fun mctx => ({ mctx := mctx } : InstantiateExprMVars.InstState σ))
    (fun s    => s.mctx)
    (InstantiateExprMVars.main e : InstantiateExprMVars.M σ Expr)

private def getOptions : ATCM σ ϕ Options :=
do ctx ← read; pure ctx.config.opts

private def getTraceState : ATCM σ ϕ TraceState :=
do s ← get; pure s.traceState

instance tracer : SimpleMonadTracerAdapter (ATCM σ ϕ) :=
{ getOptions       := getOptions,
  getTraceState    := getTraceState,
  modifyTraceState := fun f => modify $ fun s => { traceState := f s.traceState, .. s } }

end AbstractTypeContext

/- Remark: the following instance assumes all metavariables are treated as metavariables. -/
instance metavarContextIsAbstractMetavarContext : AbstractMetavarContext MetavarContext :=
{ empty                := {},
  isLevelMVar          := fun _ => true,
  getLevelAssignment   := MetavarContext.getLevelAssignment,
  assignLevel          := MetavarContext.assignLevel,
  isExprMVar           := fun _ => true,
  getExprAssignment    := MetavarContext.getExprAssignment,
  assignExpr           := MetavarContext.assignExpr,
  getExprMVarLCtx      := MetavarContext.getExprMVarLCtx,
  getExprMVarType      := MetavarContext.getExprMVarType,
  sharedContext        := false,
  assignDelayed        := MetavarContext.assignDelayed,
  getDelayedAssignment := MetavarContext.getDelayedAssignment,
  eraseDelayed         := MetavarContext.eraseDelayed
}

inductive TypeContextNoCache
| mk

instance typeContextNoCacheIsAbstractTCCache : AbstractTCCache TypeContextNoCache :=
{ getWHNF := fun _ _ _ => none,
  setWHNF := fun s _ _ _ => s
}

namespace TypeContext

-- set_option trace.compiler.ir.simp_case true

@[inline] def instantiateExprMVars (e : Expr) : State MetavarContext Expr :=
AbstractTypeContext.instantiateExprMVars e

end TypeContext

end Lean
