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
import Init.Lean.AuxRecursor
import Init.Lean.ProjFns

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

structure TypeUtilConfig :=
(opts           : Options          := {})
(unifierConfig  : UnifierConfig    := {})
(transparency   : TransparencyMode := TransparencyMode.Semireducible)
(smartUnfolding : Bool             := true)
(useZeta        : Bool             := true)

/- Abstract cache interfact for `TypeUtil` functions.
   TODO: add missing methods. -/
class AbstractTypeUtilCache (ϕ : Type) :=
(getWHNF : ϕ → TransparencyMode → Expr → Option Expr)
(setWHNF : ϕ → TransparencyMode → Expr → Expr → ϕ)

-- TODO: add special cases
inductive TypeUtilException
| other : String → TypeUtilException

structure TypeUtilContext :=
(env            : Environment)
(lctx           : LocalContext        := {})
(localInstances : LocalInstances      := #[])
(config         : TypeUtilConfig := {})

structure PostponedEntry :=
(lhs       : Level)
(updateLhs : Bool)
(rhs       : Level)
(updateRhs : Bool)

structure TypeUtilState (σ ϕ : Type) :=
(mctx           : σ)
(cache          : ϕ)
(ngen           : NameGenerator        := {})
(traceState     : TraceState           := {})
(postponed      : Array PostponedEntry := #[])

/-- Type Context Monad -/
abbrev TypeUtilM (σ ϕ : Type) := ReaderT TypeUtilContext (EState TypeUtilException (TypeUtilState σ ϕ))

namespace TypeUtil
variables {σ ϕ : Type}

private def getOptions : TypeUtilM σ ϕ Options :=
do ctx ← read; pure ctx.config.opts

private def getTraceState : TypeUtilM σ ϕ TraceState :=
do s ← get; pure s.traceState

private def getMCtx : TypeUtilM σ ϕ σ :=
do s ← get; pure s.mctx

private def getEnv : TypeUtilM σ ϕ Environment :=
do ctx ← read; pure ctx.env

private def useZeta : TypeUtilM σ ϕ Bool :=
do ctx ← read; pure ctx.config.useZeta

instance tracer : SimpleMonadTracerAdapter (TypeUtilM σ ϕ) :=
{ getOptions       := getOptions,
  getTraceState    := getTraceState,
  modifyTraceState := fun f => modify $ fun s => { traceState := f s.traceState, .. s } }

@[inline] private def liftStateMCtx {α} (x : State σ α) : TypeUtilM σ ϕ α :=
fun _ s =>
  let (a, mctx) := x.run s.mctx;
  EState.Result.ok a { mctx := mctx, .. s }

export AbstractMetavarContext (hasAssignableLevelMVar isReadOnlyLevelMVar auxMVarSupport getExprAssignment)

/- ===========================
   Weak Head Normal Form
   =========================== -/

/-- Auxiliary combinator for handling easy WHNF cases. It takes a function for handling the "hard" cases as an argument -/
@[specialize] private partial def whnfEasyCases [AbstractMetavarContext σ] : Expr → (Expr → TypeUtilM σ ϕ Expr) → TypeUtilM σ ϕ Expr
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

/-- Return true iff term is of the form `idRhs ...` -/
private def isIdRhsApp (e : Expr) : Bool :=
e.isAppOf `idRhs

/-- (@idRhs T f a_1 ... a_n) ==> (f a_1 ... a_n) -/
private def extractIdRhs (e : Expr) : Expr :=
if !isIdRhsApp e then e
else
  let args := e.getAppArgs;
  if args.size < 2 then e
  else mkAppRange (args.get! 1) 2 args.size args

@[specialize] private def deltaBetaDefinition {α} (c : ConstantInfo) (lvls : List Level) (revArgs : Array Expr) (failK : Unit → α) (successK : Expr → α) : α :=
if c.lparams.length != lvls.length then failK ()
else
  let val := c.instantiateValueLevelParams lvls;
  let val := val.betaRev revArgs;
  successK (extractIdRhs val)

/--
  Apply beta-reduction, zeta-reduction (i.e., unfold let local-decls), iota-reduction,
  expand let-expressions, expand assigned meta-variables.

  This method does *not* apply delta-reduction at the head.
  Reason: we want to perform these reductions lazily at isDefEq.

  Remark: this method delta-reduce (transparent) aux-recursors (e.g., casesOn, recOon) IF
  `reduceAuxRec == true` -/
@[specialize] private partial def whnfCore
    [AbstractMetavarContext σ]
    (whnf : Expr → TypeUtilM σ ϕ Expr)
    (inferType : Expr → TypeUtilM σ ϕ Expr)
    (isDefEq : Expr → Expr → TypeUtilM σ ϕ Bool)
    (reduceAuxRec? : Bool) : Expr → TypeUtilM σ ϕ Expr
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
      let done : Unit → TypeUtilM σ ϕ Expr := fun _ =>
        if f == f' then pure e else pure $ e.updateFn f';
      env ← getEnv;
      matchConst env f' done $ fun cinfo lvls =>
        match cinfo with
        | ConstantInfo.recInfo rec    => reduceRecAux whnf inferType isDefEq env rec lvls e.getAppArgs done whnfCore
        | ConstantInfo.quotInfo rec   => reduceQuotRecAux whnf env rec lvls e.getAppArgs done whnfCore
        | c@(ConstantInfo.defnInfo _) =>
          if reduceAuxRec? && isAuxRecursor env c.name then
            deltaBetaDefinition c lvls e.getAppArgs done whnfCore
          else
            done()
        | _ => done ()
  | e@(Expr.proj _ i c) => do
    c   ← whnf c;
    env ← getEnv;
    matchConst env c.getAppFn (fun _ => pure e) $ fun cinfo lvls =>
      match cinfo with
      | ConstantInfo.ctorInfo ctorVal => pure $ c.getArgD (ctorVal.nparams + i) e
      | _ => pure e
  | _ => unreachable!

private def whnfAux
    [AbstractMetavarContext σ]
    [AbstractTypeUtilCache ϕ]
    (whnf : Expr → TypeUtilM σ ϕ Expr)
    (inferType : Expr → TypeUtilM σ ϕ Expr)
    (isDefEq : Expr → Expr → TypeUtilM σ ϕ Bool)
    : Expr → TypeUtilM σ ϕ Expr :=
-- TODO
whnfCore whnf inferType isDefEq true

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
