/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Basic
import Lean.Meta.InferType

namespace Lean.Meta

private partial def decAux? : Level → MetaM (Option Level)
  | Level.zero _        => pure none
  | Level.param _ _     => pure none
  | Level.mvar mvarId _ => do
    let mctx ← getMCtx
    match mctx.getLevelAssignment? mvarId with
    | some u => decAux? u
    | none   =>
      if (← isReadOnlyLevelMVar mvarId) then
        pure none
      else
        let u ← mkFreshLevelMVar
        assignLevelMVar mvarId (mkLevelSucc u)
        pure u
  | Level.succ u _  => pure u
  | u =>
    let process (u v : Level) : MetaM (Option Level) := do
      match (← decAux? u) with
      | none   => pure none
      | some u => do
        match (← decAux? v) with
        | none   => pure none
        | some v => pure $ mkLevelMax' u v
    match u with
    | Level.max u v _  => process u v
    /- Remark: If `decAux? v` returns `some ...`, then `imax u v` is equivalent to `max u v`. -/
    | Level.imax u v _ => process u v
    | _                => unreachable!

variables {m : Type → Type} [MonadLiftT MetaM m]

private def decLevelImp (u : Level) : MetaM (Option Level) := do
  let mctx ← getMCtx
  match (← decAux? u) with
  | some v => pure $ some v
  | none   => do
    modify fun s => { s with mctx := mctx }
    pure none

def decLevel? (u : Level) : m (Option Level) :=
  liftMetaM $ decLevelImp u

def decLevel (u : Level) : m Level := liftMetaM do
  match (← decLevel? u) with
  | some u => pure u
  | none   => throwError! "invalid universe level, {u} is not greater than 0"

/- This method is useful for inferring universe level parameters for function that take arguments such as `{α : Type u}`.
   Recall that `Type u` is `Sort (u+1)` in Lean. Thus, given `α`, we must infer its universe level,
   and then decrement 1 to obtain `u`. -/
def getDecLevel (type : Expr) : m Level := liftMetaM do
  let u ← getLevel type
  decLevel u

private def strictOccursMaxAux (lvl : Level) : Level → Bool
  | Level.max u v _ => strictOccursMaxAux lvl u || strictOccursMaxAux lvl v
  | u               => u != lvl && lvl.occurs u

/--
  Return true iff `lvl` occurs in `max u_1 ... u_n` and `lvl != u_i` for all `i in [1, n]`.
  That is, `lvl` is a proper level subterm of some `u_i`. -/
private def strictOccursMax (lvl : Level) : Level → Bool
  | Level.max u v _ => strictOccursMaxAux lvl u || strictOccursMaxAux lvl v
  | _               => false

/-- `mkMaxArgsDiff mvarId (max u_1 ... (mvar mvarId) ... u_n) v` => `max v u_1 ... u_n` -/
private def mkMaxArgsDiff (mvarId : MVarId) : Level → Level → Level
  | Level.max u v _,     acc => mkMaxArgsDiff mvarId v $ mkMaxArgsDiff mvarId u acc
  | l@(Level.mvar id _), acc => if id != mvarId then mkLevelMax' acc l else acc
  | l,                   acc => mkLevelMax' acc l

/--
  Solve `?m =?= max ?m v` by creating a fresh metavariable `?n`
  and assigning `?m := max ?n v` -/
private def solveSelfMax (mvarId : MVarId) (v : Level) : MetaM Unit := do
  let n ← mkFreshLevelMVar
  assignLevelMVar mvarId $ mkMaxArgsDiff mvarId v n

private def postponeIsLevelDefEq (lhs : Level) (rhs : Level) : MetaM Unit :=
  modifyPostponed fun postponed => postponed.push { lhs := lhs, rhs := rhs }

mutual
private partial def solve (u v : Level) : MetaM LBool := do
  match u, v with
  | Level.mvar mvarId _, _ =>
    if (← isReadOnlyLevelMVar mvarId) then
      pure LBool.undef
    else if !u.occurs v then
      assignLevelMVar u.mvarId! v
      pure LBool.true
    else if !strictOccursMax u v then
      solveSelfMax u.mvarId! v
      pure LBool.true
    else
      pure LBool.undef
  | Level.zero _, Level.max v₁ v₂ _ =>
    Bool.toLBool <$> (isLevelDefEqAux levelZero v₁ <&&> isLevelDefEqAux levelZero v₂)
  | Level.zero _, Level.imax _ v₂ _ =>
    Bool.toLBool <$> isLevelDefEqAux levelZero v₂
  | Level.zero _, Level.succ .. => pure LBool.false
  | Level.succ u _, v =>
    match (← Meta.decLevel? v) with
    | some v => Bool.toLBool <$> isLevelDefEqAux u v
    | none   => pure LBool.undef
  | _, _ => pure LBool.undef

partial def isLevelDefEqAux : Level → Level → MetaM Bool
  | Level.succ lhs _, Level.succ rhs _ => isLevelDefEqAux lhs rhs
  | lhs, rhs => do
    if lhs == rhs then
      pure true
    else
      trace[Meta.isLevelDefEq.step]! "{lhs} =?= {rhs}"
      let lhs' ← instantiateLevelMVars lhs
      let lhs' := lhs'.normalize
      let rhs' ← instantiateLevelMVars rhs
      let rhs' := rhs'.normalize
      if lhs != lhs' || rhs != rhs' then
        isLevelDefEqAux lhs' rhs'
      else
        let r ← solve lhs rhs;
        if r != LBool.undef then
          pure $ r == LBool.true
        else
          let r ← solve rhs lhs;
          if r != LBool.undef then
            pure $ r == LBool.true
          else do
            let mctx ← getMCtx
            if !mctx.hasAssignableLevelMVar lhs && !mctx.hasAssignableLevelMVar rhs then
              let ctx ← read
              if ctx.config.isDefEqStuckEx && (lhs.isMVar || rhs.isMVar) then do
                trace[Meta.isLevelDefEq.stuck]! "{lhs} =?= {rhs}"
                Meta.throwIsDefEqStuck
              else
                pure false
            else
              postponeIsLevelDefEq lhs rhs; pure true
end

def isListLevelDefEqAux : List Level → List Level → MetaM Bool
  | [],    []    => pure true
  | u::us, v::vs => isLevelDefEqAux u v <&&> isListLevelDefEqAux us vs
  | _,     _     => pure false

private def getNumPostponed : MetaM Nat := do
  pure (← getPostponed).size

open Std (PersistentArray)

private def getResetPostponed : MetaM (PersistentArray PostponedEntry) := do
  let ps ← getPostponed
  setPostponed {}
  pure ps

private def processPostponedStep : MetaM Bool :=
  traceCtx `Meta.isLevelDefEq.postponed.step do
    let ps ← getResetPostponed
    for p in ps do
      unless (← isLevelDefEqAux p.lhs p.rhs) do
        return false
    return true

private partial def processPostponed (mayPostpone : Bool := true) : MetaM Bool := do
if (← getNumPostponed) == 0 then
  pure true
else
  traceCtx `Meta.isLevelDefEq.postponed do
    let rec loop : MetaM Bool := do
      let numPostponed ← getNumPostponed
      if numPostponed == 0 then
        pure true
      else
        trace[Meta.isLevelDefEq.postponed]! "processing #{numPostponed} postponed is-def-eq level constraints"
        if !(← processPostponedStep) then
          pure false
        else
          let numPostponed' ← getNumPostponed
          if numPostponed' == 0 then
            pure true
          else if numPostponed' < numPostponed then
            loop
          else
            trace[Meta.isLevelDefEq.postponed]! "no progress solving pending is-def-eq level constraints"
            pure mayPostpone
    loop

private def restore (env : Environment) (mctx : MetavarContext) (postponed : PersistentArray PostponedEntry) : MetaM Unit := do
  setEnv env
  setMCtx mctx
  setPostponed postponed

/--
  `commitWhen x` executes `x` and process all postponed universe level constraints produced by `x`.
  We keep the modifications only if `processPostponed` return true and `x` returned `true`.

  Remark: postponed universe level constraints must be solved before returning. Otherwise,
  we don't know whether `x` really succeeded. -/
@[specialize] def commitWhen (x : MetaM Bool) (mayPostpone : Bool := true) : MetaM Bool := do
  let env  ← getEnv
  let mctx ← getMCtx
  let postponed ← getResetPostponed
  try
    if (← x) then
      if (← processPostponed mayPostpone) then
        pure true
      else
        restore env mctx postponed
        pure false
    else
      restore env mctx postponed
      pure false
  catch ex =>
    restore env mctx postponed
    throw ex

private def postponedToMessageData (ps : PersistentArray PostponedEntry) : MessageData := do
  let mut r := MessageData.nil
  for p in ps do
    r := m!"{r}\n{p.lhs} =?= {p.rhs}"
  pure r

@[specialize] def withoutPostponingUniverseConstraintsImp {α} (x : MetaM α) : MetaM α := do
  let postponed ← getResetPostponed
  try
    let a ← x
    unless (← processPostponed (mayPostpone := false)) do
      throwError! "stuck at solving universe constraints{MessageData.nestD (postponedToMessageData (← getPostponed))}"
    setPostponed postponed
    pure a
  catch ex =>
    setPostponed postponed
    throw ex

@[inline] def withoutPostponingUniverseConstraints {α m} [MonadControlT MetaM m] [Monad m] : m α → m α :=
  mapMetaM $ withoutPostponingUniverseConstraintsImp

def isLevelDefEq (u v : Level) : m Bool := liftMetaM do
  traceCtx `Meta.isLevelDefEq do
    let b ← commitWhen (mayPostpone := true) $ Meta.isLevelDefEqAux u v
    trace[Meta.isLevelDefEq]! "{u} =?= {v} ... {if b then "success" else "failure"}"
    pure b

def isExprDefEq (t s : Expr) : m Bool := liftMetaM do
  traceCtx `Meta.isDefEq $ do
    let b ← commitWhen (mayPostpone := true) $ Meta.isExprDefEqAux t s
    trace[Meta.isDefEq]! "{t} =?= {s} ... {if b then "success" else "failure"}"
    pure b

abbrev isDefEq (t s : Expr) : m Bool :=
  isExprDefEq t s

def isExprDefEqGuarded (a b : Expr) : m Bool := liftMetaM do
  try isExprDefEq a b catch _ => pure false

abbrev isDefEqGuarded (t s : Expr) : m Bool :=
  isExprDefEqGuarded t s

def isDefEqNoConstantApprox (t s : Expr) : m Bool := liftMetaM do
  approxDefEq $ isDefEq t s

builtin_initialize
  registerTraceClass `Meta.isLevelDefEq
  registerTraceClass `Meta.isLevelDefEq.step
  registerTraceClass `Meta.isLevelDefEq.postponed

end Lean.Meta
