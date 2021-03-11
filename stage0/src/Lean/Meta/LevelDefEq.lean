/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Basic
import Lean.Meta.InferType

namespace Lean.Meta

private partial def decAux? : Level → MetaM (Option Level)
  | Level.zero _        => return none
  | Level.param _ _     => return none
  | Level.mvar mvarId _ => do
    let mctx ← getMCtx
    match mctx.getLevelAssignment? mvarId with
    | some u => decAux? u
    | none   =>
      if (← isReadOnlyLevelMVar mvarId) then
        return none
      else
        let u ← mkFreshLevelMVar
        assignLevelMVar mvarId (mkLevelSucc u)
        return u
  | Level.succ u _  => return u
  | u =>
    let process (u v : Level) : MetaM (Option Level) := do
      match (← decAux? u) with
      | none   => return none
      | some u => do
        match (← decAux? v) with
        | none   => return none
        | some v => return mkLevelMax' u v
    match u with
    | Level.max u v _  => process u v
    /- Remark: If `decAux? v` returns `some ...`, then `imax u v` is equivalent to `max u v`. -/
    | Level.imax u v _ => process u v
    | _                => unreachable!

def decLevel? (u : Level) : MetaM (Option Level) := do
  let mctx ← getMCtx
  match (← decAux? u) with
  | some v => return some v
  | none   => do
    modify fun s => { s with mctx := mctx }
    return none

def decLevel (u : Level) : MetaM Level := do
  match (← decLevel? u) with
  | some u => return u
  | none   => throwError! "invalid universe level, {u} is not greater than 0"

/- This method is useful for inferring universe level parameters for function that take arguments such as `{α : Type u}`.
   Recall that `Type u` is `Sort (u+1)` in Lean. Thus, given `α`, we must infer its universe level,
   and then decrement 1 to obtain `u`. -/
def getDecLevel (type : Expr) : MetaM Level := do
  decLevel (← getLevel type)

/--
  Return true iff `lvl` occurs in `max u_1 ... u_n` and `lvl != u_i` for all `i in [1, n]`.
  That is, `lvl` is a proper level subterm of some `u_i`. -/
private def strictOccursMax (lvl : Level) : Level → Bool
  | Level.max u v _ => visit u || visit v
  | _               => false
where
  visit : Level → Bool
    | Level.max u v _ => visit u || visit v
    | u               => u != lvl && lvl.occurs u

/-- `mkMaxArgsDiff mvarId (max u_1 ... (mvar mvarId) ... u_n) v` => `max v u_1 ... u_n` -/
private def mkMaxArgsDiff (mvarId : MVarId) : Level → Level → Level
  | Level.max u v _,     acc => mkMaxArgsDiff mvarId v <| mkMaxArgsDiff mvarId u acc
  | l@(Level.mvar id _), acc => if id != mvarId then mkLevelMax' acc l else acc
  | l,                   acc => mkLevelMax' acc l

/--
  Solve `?m =?= max ?m v` by creating a fresh metavariable `?n`
  and assigning `?m := max ?n v` -/
private def solveSelfMax (mvarId : MVarId) (v : Level) : MetaM Unit := do
  assert! v.isMax
  let n ← mkFreshLevelMVar
  assignLevelMVar mvarId <| mkMaxArgsDiff mvarId v n

private def postponeIsLevelDefEq (lhs : Level) (rhs : Level) : MetaM Unit :=
  modifyPostponed fun postponed => postponed.push { lhs := lhs, rhs := rhs }

mutual

  private partial def solve (u v : Level) : MetaM LBool := do
    match u, v with
    | Level.mvar mvarId _, _ =>
      if (← isReadOnlyLevelMVar mvarId) then
        return LBool.undef
      else if !u.occurs v then
        assignLevelMVar u.mvarId! v
        return LBool.true
      else if v.isMax && !strictOccursMax u v then
        solveSelfMax u.mvarId! v
        return LBool.true
      else
        return LBool.undef
    | Level.zero _, Level.max v₁ v₂ _ =>
      Bool.toLBool <$> (isLevelDefEqAux levelZero v₁ <&&> isLevelDefEqAux levelZero v₂)
    | Level.zero _, Level.imax _ v₂ _ =>
      Bool.toLBool <$> isLevelDefEqAux levelZero v₂
    | Level.zero _, Level.succ .. => return LBool.false
    | Level.succ u _, v =>
      if u.isMVar && u.occurs v then
        return LBool.undef
      else
        match (← Meta.decLevel? v) with
        | some v => Bool.toLBool <$> isLevelDefEqAux u v
        | none   => return LBool.undef
    | _, _ => return LBool.undef

  partial def isLevelDefEqAux : Level → Level → MetaM Bool
    | Level.succ lhs _, Level.succ rhs _ => isLevelDefEqAux lhs rhs
    | lhs, rhs => do
      if lhs.getLevelOffset == rhs.getLevelOffset then
        return lhs.getOffset == rhs.getOffset
      else
        trace[Meta.isLevelDefEq.step] "{lhs} =?= {rhs}"
        let lhs' ← instantiateLevelMVars lhs
        let lhs' := lhs'.normalize
        let rhs' ← instantiateLevelMVars rhs
        let rhs' := rhs'.normalize
        if lhs != lhs' || rhs != rhs' then
          isLevelDefEqAux lhs' rhs'
        else
          let r ← solve lhs rhs;
          if r != LBool.undef then
            return r == LBool.true
          else
            let r ← solve rhs lhs;
            if r != LBool.undef then
              return r == LBool.true
            else do
              let mctx ← getMCtx
              if !mctx.hasAssignableLevelMVar lhs && !mctx.hasAssignableLevelMVar rhs then
                let ctx ← read
                if ctx.config.isDefEqStuckEx && (lhs.isMVar || rhs.isMVar) then do
                  trace[Meta.isLevelDefEq.stuck] "{lhs} =?= {rhs}"
                  Meta.throwIsDefEqStuck
                else
                  return false
              else
                postponeIsLevelDefEq lhs rhs
                return true
end

def isListLevelDefEqAux : List Level → List Level → MetaM Bool
  | [],    []    => return true
  | u::us, v::vs => isLevelDefEqAux u v <&&> isListLevelDefEqAux us vs
  | _,     _     => return false

private def getNumPostponed : MetaM Nat := do
  return (← getPostponed).size

open Std (PersistentArray)

private def getResetPostponed : MetaM (PersistentArray PostponedEntry) := do
  let ps ← getPostponed
  setPostponed {}
  return ps

private def processPostponedStep : MetaM Bool :=
  traceCtx `Meta.isLevelDefEq.postponed.step do
    let ps ← getResetPostponed
    for p in ps do
      unless (← isLevelDefEqAux p.lhs p.rhs) do
        return false
    return true

private partial def processPostponed (mayPostpone : Bool := true) : MetaM Bool := do
if (← getNumPostponed) == 0 then
  return true
else
  traceCtx `Meta.isLevelDefEq.postponed do
    let rec loop : MetaM Bool := do
      let numPostponed ← getNumPostponed
      if numPostponed == 0 then
        return true
      else
        trace[Meta.isLevelDefEq.postponed] "processing #{numPostponed} postponed is-def-eq level constraints"
        if !(← processPostponedStep) then
          return false
        else
          let numPostponed' ← getNumPostponed
          if numPostponed' == 0 then
            return true
          else if numPostponed' < numPostponed then
            loop
          else
            trace[Meta.isLevelDefEq.postponed] "no progress solving pending is-def-eq level constraints"
            return mayPostpone
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
        let newPostponed ← getPostponed
        setPostponed (postponed ++ newPostponed)
        return true
      else
        restore env mctx postponed
        return false
    else
      restore env mctx postponed
      return false
  catch ex =>
    restore env mctx postponed
    throw ex

private def postponedToMessageData (ps : PersistentArray PostponedEntry) : MessageData := do
  let mut found : Std.HashSet (Level × Level) := {}
  let mut r := MessageData.nil
  for p in ps do
    let mut lhs := p.lhs
    let mut rhs := p.rhs
    if Level.normLt rhs lhs then
      (lhs, rhs) := (rhs, lhs)
    unless found.contains (lhs, rhs) do
      found := found.insert (lhs, rhs)
      r := m!"{r}\n{lhs} =?= {rhs}"
  return r

@[specialize] def withoutPostponingUniverseConstraintsImp {α} (x : MetaM α) : MetaM α := do
  let postponed ← getResetPostponed
  try
    let a ← x
    unless (← processPostponed (mayPostpone := false)) do
      throwError! "stuck at solving universe constraints{MessageData.nestD (postponedToMessageData (← getPostponed))}"
    setPostponed postponed
    return a
  catch ex =>
    setPostponed postponed
    throw ex

@[inline] def withoutPostponingUniverseConstraints {α m} [MonadControlT MetaM m] [Monad m] : m α → m α :=
  mapMetaM <| withoutPostponingUniverseConstraintsImp

def isLevelDefEq (u v : Level) : MetaM Bool :=
  traceCtx `Meta.isLevelDefEq do
    let b ← commitWhen (mayPostpone := true) <| Meta.isLevelDefEqAux u v
    trace[Meta.isLevelDefEq] "{u} =?= {v} ... {if b then "success" else "failure"}"
    return b

def isExprDefEq (t s : Expr) : MetaM Bool :=
  traceCtx `Meta.isDefEq do
    let b ← commitWhen (mayPostpone := true) <| Meta.isExprDefEqAux t s
    trace[Meta.isDefEq] "{t} =?= {s} ... {if b then "success" else "failure"}"
    return b

abbrev isDefEq (t s : Expr) : MetaM Bool :=
  isExprDefEq t s

def isExprDefEqGuarded (a b : Expr) : MetaM Bool := do
  try isExprDefEq a b catch _ => return false

abbrev isDefEqGuarded (t s : Expr) : MetaM Bool :=
  isExprDefEqGuarded t s

def isDefEqNoConstantApprox (t s : Expr) : MetaM Bool :=
  approxDefEq <| isDefEq t s

builtin_initialize
  registerTraceClass `Meta.isLevelDefEq
  registerTraceClass `Meta.isLevelDefEq.step
  registerTraceClass `Meta.isLevelDefEq.postponed

end Lean.Meta
