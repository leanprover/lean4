/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.LocalContext

namespace Lean
/--
  A delayed assignment for a metavariable `?m`. It represents an assignment of the form
  `?m := (fun fvars => val)`. The local context `lctx` provides the declarations for `fvars`.
  Note that `fvars` may not be defined in the local context for `?m`. -/
structure DelayedMVarAssignment :=
(lctx     : LocalContext)
(fvars    : Array Expr)
(val      : Expr)

/--
  We can `TypeContext` functions with different implementations of
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

namespace AbstractMetavarContext

variables {σ : Type}

@[inline] def isLevelAssigned [AbstractMetavarContext σ] (mctx : σ) (mvarId : Name) : Bool :=
(getLevelAssignment mctx mvarId).isSome

@[inline] def isExprAssigned [AbstractMetavarContext σ] (mctx : σ) (mvarId : Name) : Bool :=
(getExprAssignment mctx mvarId).isSome

def hasAssignedLevelMVar [AbstractMetavarContext σ] (mctx : σ) : Level → Bool
| Level.succ lvl       => lvl.hasMVar && hasAssignedLevelMVar lvl
| Level.max lvl₁ lvl₂  => (lvl₁.hasMVar && hasAssignedLevelMVar lvl₁) || (lvl₂.hasMVar && hasAssignedLevelMVar lvl₂)
| Level.imax lvl₁ lvl₂ => (lvl₁.hasMVar && hasAssignedLevelMVar lvl₁) || (lvl₂.hasMVar && hasAssignedLevelMVar lvl₂)
| Level.mvar mvarId    => isLevelAssigned mctx mvarId
| Level.zero           => false
| Level.param _        => false

/-- Return `true` iff expression contains assigned (level/expr) metavariables -/
def hasAssignedMVar [AbstractMetavarContext σ] (mctx : σ) : Expr → Bool
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

partial def instantiateLevelMVars [AbstractMetavarContext σ] : Level → State σ Level
| lvl@(Level.succ lvl₁)       => do lvl₁ ← instantiateLevelMVars lvl₁; pure (Level.updateSucc! lvl lvl₁)
| lvl@(Level.max lvl₁ lvl₂)   => do lvl₁ ← instantiateLevelMVars lvl₁; lvl₂ ← instantiateLevelMVars lvl₂; pure (Level.updateMax! lvl lvl₁ lvl₂)
| lvl@(Level.imax lvl₁ lvl₂)  => do lvl₁ ← instantiateLevelMVars lvl₁; lvl₂ ← instantiateLevelMVars lvl₂; pure (Level.updateIMax! lvl lvl₁ lvl₂)
| lvl@(Level.mvar mvarId) => do
  mctx ← get;
  match getLevelAssignment mctx mvarId with
  | some newLvl =>
    if !newLvl.hasMVar then pure newLvl
    else do
      newLvl' ← instantiateLevelMVars newLvl;
      modify $ fun mctx => assignLevel mctx mvarId newLvl';
      pure newLvl'
  | none        => pure lvl
| lvl => pure lvl

namespace InstantiateExprMVars
/-- Auxiliary structure for instantiating metavariables in `Expr`s. -/
structure InstState (σ : Type) :=
(mctx  : σ)
(cache : ExprMap Expr := {})

abbrev M (σ : Type) := State (InstState σ)

@[inline] def instantiateLevelMVars [AbstractMetavarContext σ] (lvl : Level) : M σ Level :=
adaptState
  (fun (s : InstState σ) => (s.mctx, { mctx := empty σ, .. s }))
  (fun (mctx : σ) (s : InstState σ) => { mctx := mctx, .. s })
  (AbstractMetavarContext.instantiateLevelMVars lvl : State σ Level)

@[inline] def checkCache (e : Expr) (f : Expr → M σ Expr) : M σ Expr :=
do s ← get;
   match s.cache.find e with
   | some r => pure r
   | none => do
     r ← f e;
     modify $ fun s => { cache := s.cache.insert e r, .. s };
     pure r

@[inline] def visit (f : Expr → M σ Expr) (e : Expr) : M σ Expr :=
if !e.hasMVar then pure e else checkCache e f

@[inline] def getMCtx : M σ σ :=
do s ← get; pure s.mctx

/--
  Auxiliary function for `instantiateDelayed`.
  `instantiateDelayed main lctx fvars i body` is used to create `fun fvars[0, i) => body`.
  It fails if one of variable declarations in `fvars` still contains unassigned metavariables.

  Pre: all expressions in `fvars` are `Expr.fvar`, and `lctx` contains their declarations. -/
@[specialize] def instantiateDelayedAux [AbstractMetavarContext σ] (main : Expr → M σ Expr) (lctx : LocalContext) (fvars : Array Expr)
                  : Nat → Expr → M σ (Option Expr)
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
@[inline] def instantiateDelayed [AbstractMetavarContext σ] (main : Expr → M σ Expr) (mvarId : Name) : DelayedMVarAssignment → M σ (Option Expr)
| { lctx := lctx, fvars := fvars, val := val } => do
  newVal ← visit main val;
  let fail : M σ (Option Expr) := do {
     /- Join point for updating delayed assignment and failing -/
     modify $ fun s => { mctx := assignDelayed s.mctx mvarId lctx fvars newVal, .. s };
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
        { mctx := assignExpr (eraseDelayed s.mctx mvarId) mvarId newE, .. s };
      pure (some newE)

/-- instantiateExprMVars main function -/
partial def main [AbstractMetavarContext σ] : Expr → M σ Expr
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
  match getExprAssignment mctx mvarId with
  | some newE => do
    newE' ← visit main newE;
    modify $ fun s => { mctx := assignExpr s.mctx mvarId newE', .. s };
    pure newE'
  | none =>
    /- A delayed assignment can be transformed into a regular assignment
       as soon as all metavariables occurring in the assigned value have
       been assigned. -/
    match getDelayedAssignment mctx mvarId with
    | some d => do
       newE ← instantiateDelayed main mvarId d;
       pure $ newE.getD e
    | none   => pure e
| e => pure e

end InstantiateExprMVars

def instantiateMVars [AbstractMetavarContext σ] (e : Expr) : State σ Expr :=
if !e.hasMVar then pure e
else
  adaptState'
    (fun mctx => ({ mctx := mctx } : InstantiateExprMVars.InstState σ))
    (fun s    => s.mctx)
    (InstantiateExprMVars.main e : InstantiateExprMVars.M σ Expr)

end AbstractMetavarContext

end Lean
