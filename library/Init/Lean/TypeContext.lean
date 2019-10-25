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
(assignDelayed        (mctx : σ) (mvarId : Name) (lctx : LocalContext) (fvars : List Expr) (val : Expr) : σ)
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
| lvl@(Level.succ lvl₁)       => Level.updateSucc! lvl <$> instantiateLevelMVars lvl₁
| lvl@(Level.max lvl₁ lvl₂)   => Level.updateMax! lvl <$> instantiateLevelMVars lvl₁ <*> instantiateLevelMVars lvl₂
| lvl@(Level.imax lvl₁ lvl₂)  => Level.updateIMax! lvl <$> instantiateLevelMVars lvl₁ <*> instantiateLevelMVars lvl₂
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

/-- instantiateExprMVars main function -/
partial def main {σ} [AbstractMetavarContext σ] : Expr → M σ Expr
| e@(Expr.proj _ _ s)      => e.updateProj! <$> visit main s
| e@(Expr.forallE _ _ d b) => e.updateForallE! <$> visit main d <*> visit main b
| e@(Expr.lam _ _ d b)     => e.updateLambdaE! <$> visit main d <*> visit main b
| e@(Expr.letE _ t v b)    => e.updateLet! <$> visit main t <*> visit main v <*> visit main b
| e@(Expr.const _ lvls)    => e.updateConst! <$> lvls.mmap instantiateLevelMVars
| e@(Expr.sort lvl)        => e.updateSort! <$> instantiateLevelMVars lvl
| e@(Expr.mdata _ b)       => e.updateMData! <$> visit main b
| e@(Expr.app f a)         =>
  -- TODO apply beta
  e.updateApp! <$> visit main f <*> visit main a
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
    | some { lctx := lctx, fvars := fvars, val := val } => do
      newVal ← visit main val;
      if newVal.hasMVar then do
        modify $ fun s => { mctx := AbstractMetavarContext.assignDelayed s.mctx mvarId lctx fvars newVal, .. s };
        pure e
      else
        -- TODO: abstract newVal and ensure fvars decls do not contain metavars
        pure e
    | none   => pure e
| e => pure e

end InstantiateExprMVars

def instantiateExprMVars {σ} [AbstractMetavarContext σ] (e : Expr) : State σ Expr :=
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

end Lean
