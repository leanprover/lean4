/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Control.Reader
import Init.Lean.NameGenerator
import Init.Lean.Environment
import Init.Lean.AbstractMetavarContext
import Init.Lean.Trace
import Init.Lean.InductiveUtil
import Init.Lean.QuotUtil

/-
This module provides three (mutually dependent) goodies:
1- Weak head normal form computation with support for metavariables and transparency modes.
2- Definitionally equality checking with support for metavariables (aka unification modulo definitional equality).
3- Type inference.
-/

namespace Lean
inductive TransparencyMode
| All | Semireducible | Instances | Reducible | None

structure LocalInstance :=
(className : Name)
(fvar      : Expr)

abbrev LocalInstances := Array LocalInstance

structure UnifierConfig :=
(foApprox           : Bool := false)
(ctxApprox          : Bool := false)
(quasiPatternApprox : Bool := false)

structure TypeInferenceConfig :=
(opts           : Options          := {})
(unifierConfig  : UnifierConfig    := {})
(transparency   : TransparencyMode := TransparencyMode.Semireducible)
(smartUnfolding : Bool             := true)
(useZeta        : Bool             := true)

/- Abstract cache interfact for `TypeInference` functions.
   TODO: add missing methods. -/
class AbstractTypeInferenceCache (ϕ : Type) :=
(getWHNF : ϕ → TransparencyMode → Expr → Option Expr)
(setWHNF : ϕ → TransparencyMode → Expr → Expr → ϕ)

-- TODO: add special cases
inductive TypeInferenceException
| other : String → TypeInferenceException

structure TypeInferenceContext :=
(env            : Environment)
(lctx           : LocalContext        := {})
(localInstances : LocalInstances      := #[])
(config         : TypeInferenceConfig := {})

structure PostponedEntry :=
(lhs       : Level)
(updateLhs : Bool)
(rhs       : Level)
(updateRhs : Bool)

structure TypeInferenceState (σ ϕ : Type) :=
(mctx           : σ)
(cache          : ϕ)
(ngen           : NameGenerator        := {})
(traceState     : TraceState           := {})
(postponed      : Array PostponedEntry := #[])

/-- Type Context Monad -/
abbrev TypeInferenceM (σ ϕ : Type) := ReaderT TypeInferenceContext (EState TypeInferenceException (TypeInferenceState σ ϕ))

namespace TypeInference
variables {σ ϕ : Type}

private def getOptions : TypeInferenceM σ ϕ Options :=
do ctx ← read; pure ctx.config.opts

private def getTraceState : TypeInferenceM σ ϕ TraceState :=
do s ← get; pure s.traceState

private def getMCtx : TypeInferenceM σ ϕ σ :=
do s ← get; pure s.mctx

private def getEnv : TypeInferenceM σ ϕ Environment :=
do ctx ← read; pure ctx.env

private def useZeta : TypeInferenceM σ ϕ Bool :=
do ctx ← read; pure ctx.config.useZeta

instance tracer : SimpleMonadTracerAdapter (TypeInferenceM σ ϕ) :=
{ getOptions       := getOptions,
  getTraceState    := getTraceState,
  modifyTraceState := fun f => modify $ fun s => { traceState := f s.traceState, .. s } }

@[inline] private def liftStateMCtx {α} (x : State σ α) : TypeInferenceM σ ϕ α :=
fun _ s =>
  let (a, mctx) := x.run s.mctx;
  EState.Result.ok a { mctx := mctx, .. s }

export AbstractMetavarContext (hasAssignableLevelMVar isReadOnlyLevelMVar auxMVarSupport getExprAssignment)

/- ===========================
   Weak Head Normal Form
   =========================== -/

/-- Auxiliary combinator for handling easy WHNF cases. It takes a function for handling the "hard" cases as an argument -/
@[specialize] private partial def whnfEasyCases [AbstractMetavarContext σ] : Expr → (Expr → TypeInferenceM σ ϕ Expr) → TypeInferenceM σ ϕ Expr
| e@(Expr.forallE _ _ _ _), _ => pure e
| e@(Expr.lam _ _ _ _),     _ => pure e
| e@(Expr.sort _),          _ => pure e
| e@(Expr.lit _),           _ => pure e
| e@(Expr.bvar _),          _ => unreachable!
| Expr.mdata _ e,           k => whnfEasyCases e k
| e@(Expr.letE _ _ _ _),    k => do
  c ← useZeta;
  if c then k e else pure e
| e@(Expr.fvar fvarId),     k => do
  ctx ← read;
  let ldecl := (ctx.lctx.find fvarId).get!;
  match ldecl.valueOpt with
  | none   => pure e
  | some v => do
    c ← useZeta;
    if c then
      whnfEasyCases v k
    else
      pure e
| e@(Expr.mvar mvarId),     k => do
  mctx ← getMCtx;
  match getExprAssignment mctx mvarId with
  | some v => whnfEasyCases v k
  | none   => pure e
| e@(Expr.const _ _),       k => k e
| e@(Expr.app _ _),         k => k e
| e@(Expr.proj _ _ _),      k => k e

/--
  Apply beta-reduction, zeta-reduction (i.e., unfold let local-decls), iota-reduction,
  expand let-expressions, expand assigned meta-variables.

  This method does *not* apply delta-reduction at the head.
  Reason: we want to perform these reductions lazily at isDefEq.

  Remark: this method delta-reduce (transparent) aux-recursors (e.g., casesOn, recOon) IF
  `reduceAuxRec == true` -/
@[specialize] private partial def whnfCore
    [AbstractMetavarContext σ]
    (whnf : Expr → TypeInferenceM σ ϕ Expr)
    (inferType : Expr → TypeInferenceM σ ϕ Expr)
    (isDefEq : Expr → Expr → TypeInferenceM σ ϕ Bool)
    (reduceAuxRec : Bool) : Expr → TypeInferenceM σ ϕ Expr
| e => whnfEasyCases e $ fun e =>
  match e with
  | e@(Expr.const _ _)    => pure e
  | e@(Expr.letE _ _ v b) => whnfCore $ b.instantiate1 v
  | e@(Expr.app f _)      => do
    let f := f.getAppFn;
    f' ← whnfCore f;
    if f'.isLambda then
      let revArgs := e.getAppRevArgs;
      whnfCore $ f.betaRev revArgs
    else do
      let done : Unit → TypeInferenceM σ ϕ Expr := fun _ =>
        if f == f' then pure e else pure $ e.updateFn f';
      env ← getEnv;
      matchConst env f' done $ fun cinfo lvls =>
        match cinfo with
        | ConstantInfo.recInfo rec => do
          r ← reduceRecAux whnf inferType isDefEq env rec lvls e.getAppArgs;
          match r with
          | some newE => whnfCore newE
          | none      => done ()
        | ConstantInfo.quotInfo rec => do
          r ← reduceQuotRecAux whnf env rec lvls e.getAppArgs;
          match r with
          | some newE => whnfCore newE
          | none      => done ()
        | _ =>
         -- TODO: auxiliary recursors
         done ()
  | e@(Expr.proj _ i m) => do
    m ← whnf m;
    let f := m.getAppFn;
    -- TODO check if `f` is constructor and reduce
    pure e
  | _                     => unreachable!

/- ===========================
   isDefEq for universe levels
   =========================== -/

private def instantiateLevelMVars [AbstractMetavarContext σ] (lvl : Level) : TypeInferenceM σ ϕ Level :=
liftStateMCtx $ AbstractMetavarContext.instantiateLevelMVars lvl

private def assignLevel [AbstractMetavarContext σ] (mvarId : Name) (lvl : Level) : TypeInferenceM σ ϕ Unit :=
modify $ fun s => { mctx := AbstractMetavarContext.assignLevel s.mctx mvarId lvl, .. s }

private def mkFreshLevelMVar [AbstractMetavarContext σ] : TypeInferenceM σ ϕ Level :=
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
private def solveSelfMax [AbstractMetavarContext σ] (mvarId : Name) (v : Level) : TypeInferenceM σ ϕ Unit :=
do n ← mkFreshLevelMVar;
   let lhs := mkMaxArgsDiff mvarId v n;
   assignLevel mvarId lhs

private def postponeIsLevelDefEq (lhs : Level) (updateLhs : Bool) (rhs : Level) (updateRhs : Bool) : TypeInferenceM σ ϕ Unit :=
modify $ fun s => { postponed := s.postponed.push { lhs := lhs, updateLhs := updateLhs, rhs := rhs, updateRhs := updateRhs }, .. s }

private partial def isLevelDefEqAux [AbstractMetavarContext σ] (updateLhs updateRhs : Bool) : Level → Level → TypeInferenceM σ ϕ Bool
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

private def getNumPostponed : TypeInferenceM σ ϕ Nat :=
do s ← get;
   pure s.postponed.size

private def getResetPostponed : TypeInferenceM σ ϕ (Array PostponedEntry) :=
do s ← get;
   let ps := s.postponed;
   modify $ fun s => { postponed := #[], .. s };
   pure ps

private def processPostponedStep [AbstractMetavarContext σ] : TypeInferenceM σ ϕ Bool :=
traceCtx `type_context.level_is_def_eq.postponed_step $ do
  ps ← getResetPostponed;
  ps.foldlM
    (fun (r : Bool) (p : PostponedEntry) =>
      if r then
        isLevelDefEqAux p.updateLhs p.updateRhs p.lhs p.rhs
      else
        pure false)
    true

private partial def processPostponedAux [AbstractMetavarContext σ] : Bool → TypeInferenceM σ ϕ Bool
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

private def processPostponed [AbstractMetavarContext σ] (mayPostpone : Bool) : TypeInferenceM σ ϕ Bool :=
do numPostponed ← getNumPostponed;
   if numPostponed == 0 then pure true
   else traceCtx `type_context.level_is_def_eq.postponed $ processPostponedAux mayPostpone

@[inline] private def restoreIfFalse (x : TypeInferenceM σ ϕ Bool) : TypeInferenceM σ ϕ Bool :=
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



/- Public interface -/

def isLevelDefEq [AbstractMetavarContext σ] (u v : Level) (mayPostpone : Bool := false) : TypeInferenceM σ ϕ Bool :=
restoreIfFalse $ do
  r ← isLevelDefEqAux true true u v;
  if !r then pure false
  else processPostponed mayPostpone

end TypeInference

inductive TypeInferenceNoCache
| mk

instance typeContextNoCacheIsAbstractTCCache : AbstractTypeInferenceCache TypeInferenceNoCache :=
{ getWHNF := fun _ _ _ => none,
  setWHNF := fun s _ _ _ => s }

end Lean
