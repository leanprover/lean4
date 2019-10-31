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
(lctx           : LocalContext)
(localInstances : LocalInstances)
(config         : TypeInferenceConfig := {})

structure PostponedEntry :=
(lhs       : Level)
(updateLhs : Bool)
(rhs       : Level)
(updateRhs : Bool)

structure TypeInferenceState (σ ϕ : Type) :=
(mctx           : σ)
(cache          : ϕ)
(ngen           : NameGenerator)
(traceState     : TraceState)
(usedAssignment : Bool := false)
(postponed      : Array PostponedEntry := #[])

instance TypeInferenceState.backtrackable {σ ϕ} : EState.Backtrackable σ (TypeInferenceState σ ϕ) :=
{ save    := fun s => s.mctx,
  restore := fun s mctx => { mctx := mctx, .. s } }

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

instance tracer : SimpleMonadTracerAdapter (TypeInferenceM σ ϕ) :=
{ getOptions       := getOptions,
  getTraceState    := getTraceState,
  modifyTraceState := fun f => modify $ fun s => { traceState := f s.traceState, .. s } }

@[inline] private def liftStateMCtx {α} (x : State σ α) : TypeInferenceM σ ϕ α :=
fun _ s =>
  let (a, mctx) := x.run s.mctx;
  EState.Result.ok a { mctx := mctx, .. s }

private def instantiateLevelMVars [AbstractMetavarContext σ] (lvl : Level) : TypeInferenceM σ ϕ Level :=
liftStateMCtx $ AbstractMetavarContext.instantiateLevelMVars lvl

private def assignLevel [AbstractMetavarContext σ] (mvarId : Name) (lvl : Level) : TypeInferenceM σ ϕ Unit :=
modify $ fun s => { mctx := AbstractMetavarContext.assignLevel s.mctx mvarId lvl, .. s }

export AbstractMetavarContext (hasAssignableLevelMVar isReadOnlyLevelMVar auxMVarSupport)

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

private def postponeIsLevelDefEq (postpone : Bool) (lhs : Level) (updateLhs : Bool) (rhs : Level) (updateRhs : Bool) : TypeInferenceM σ ϕ Bool :=
if postpone then do
  modify $ fun s => { postponed := s.postponed.push { lhs := lhs, updateLhs := updateLhs, rhs := rhs, updateRhs := updateRhs }, .. s };
  pure true
else
  pure false

private partial def isLevelDefEqAux [AbstractMetavarContext σ] (updateLhs updateRhs postpone : Bool) : Level → Level → TypeInferenceM σ ϕ Bool
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
          | _,         _         => postponeIsLevelDefEq postpone lhs updateLhs rhs updateRhs
        else
          postponeIsLevelDefEq postpone lhs updateLhs rhs updateRhs

end TypeInference

inductive TypeInferenceNoCache
| mk

instance typeContextNoCacheIsAbstractTCCache : AbstractTypeInferenceCache TypeInferenceNoCache :=
{ getWHNF := fun _ _ _ => none,
  setWHNF := fun s _ _ _ => s }

end Lean
