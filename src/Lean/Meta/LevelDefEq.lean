/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Util.CollectMVars
import Lean.Util.ReplaceExpr
import Lean.Meta.Basic
import Lean.Meta.InferType

namespace Lean.Meta

structure DecLevelContext where
  /--
   If `true`, then `decAux? ?m` returns a fresh metavariable `?n` s.t.
   `?m := ?n+1`.
   -/
  canAssignMVars : Bool := true

private partial def decAux? : Level → ReaderT DecLevelContext MetaM (Option Level)
  | Level.zero _        => return none
  | Level.param _ _     => return none
  | Level.mvar mvarId _ => do
    let mctx ← getMCtx
    match mctx.getLevelAssignment? mvarId with
    | some u => decAux? u
    | none   =>
      if (← isReadOnlyLevelMVar mvarId) || !(← read).canAssignMVars then
        return none
      else
        let u ← mkFreshLevelMVar
        trace[Meta.isLevelDefEq.step] "decAux?, {mkLevelMVar mvarId} := {mkLevelSucc u}"
        assignLevelMVar mvarId (mkLevelSucc u)
        return u
  | Level.succ u _  => return u
  | u =>
    let processMax (u v : Level) : ReaderT DecLevelContext MetaM (Option Level) := do
      /- Remark: this code uses the fact that `max (u+1) (v+1) = (max u v)+1`.
         `decAux? (max (u+1) (v+1)) := max (decAux? (u+1)) (decAux? (v+1))`
         However, we must *not* assign metavariables in the recursive calls since
         `max ?u 1` is not equivalent to `max ?v 0` where `?v` is a fresh metavariable, and `?u := ?v+1`
       -/
      withReader (fun _ => { canAssignMVars := false }) do
        match (← decAux? u) with
        | none   => return none
        | some u => do
          match (← decAux? v) with
          | none   => return none
          | some v => return mkLevelMax' u v
    match u with
    | Level.max u v _  => processMax u v
    /- Remark: If `decAux? v` returns `some ...`, then `imax u v` is equivalent to `max u v`. -/
    | Level.imax u v _ => processMax u v
    | _                => unreachable!

def decLevel? (u : Level) : MetaM (Option Level) := do
  let mctx ← getMCtx
  match (← decAux? u |>.run {}) with
  | some v => return some v
  | none   => do
    modify fun s => { s with mctx := mctx }
    return none

def decLevel (u : Level) : MetaM Level := do
  match (← decLevel? u) with
  | some u => return u
  | none   => throwError "invalid universe level, {u} is not greater than 0"

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

private def postponeIsLevelDefEq (lhs : Level) (rhs : Level) : MetaM Unit := do
  let ref ← getRef
  let ctx ← read
  trace[Meta.isLevelDefEq.stuck] "{lhs} =?= {rhs}"
  modifyPostponed fun postponed => postponed.push { lhs := lhs, rhs := rhs, ref := ref, ctx? := ctx.defEqCtx? }

private def isMVarWithGreaterDepth (v : Level) (mvarId : MVarId) : MetaM Bool :=
  match v with
  | Level.mvar mvarId' _ => return (← getLevelMVarDepth mvarId') > (← getLevelMVarDepth mvarId)
  | _ => return false

mutual

  private partial def solve (u v : Level) : MetaM LBool := do
    match u, v with
    | Level.mvar mvarId _, _ =>
      if (← isReadOnlyLevelMVar mvarId) then
        return LBool.undef
      else if (← getConfig).ignoreLevelMVarDepth && (← isMVarWithGreaterDepth v mvarId) then
        -- If both `u` and `v` are both metavariables, but depth of v is greater, then we assign `v := u`.
        -- This can only happen when `ignoreLevelDepth` is set to true.
        assignLevelMVar v.mvarId! u
        return LBool.true
      else if !u.occurs v then
        assignLevelMVar u.mvarId! v
        return LBool.true
      else if v.isMax && !strictOccursMax u v then
        solveSelfMax u.mvarId! v
        return LBool.true
      else
        return LBool.undef
    | _, Level.mvar .. => LBool.undef -- Let `solve v u` to handle this case
    | Level.zero _, Level.max v₁ v₂ _ =>
      Bool.toLBool <$> (isLevelDefEqAux levelZero v₁ <&&> isLevelDefEqAux levelZero v₂)
    | Level.zero _, Level.imax _ v₂ _ =>
      Bool.toLBool <$> isLevelDefEqAux levelZero v₂
    | Level.zero _, Level.succ .. => return LBool.false
    | Level.succ u _, v =>
      if v.isParam then
        return LBool.false
      else if u.isMVar && u.occurs v then
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

def getResetPostponed : MetaM (PersistentArray PostponedEntry) := do
  let ps ← getPostponed
  setPostponed {}
  return ps

/-- Annotate any constant and sort in `e` that satisfies `p` with `pp.universes true` -/
private def exposeRelevantUniverses (e : Expr) (p : Level → Bool) : Expr :=
  e.replace fun
    | Expr.const _ us _ => if us.any p then some (e.setPPUniverses true) else none
    | Expr.sort u _     => if p u then some (e.setPPUniverses true) else none
    | _                 => none

private def mkLeveErrorMessageCore (header : String) (entry : PostponedEntry) : MetaM MessageData := do
  match entry.ctx? with
  | none =>
    return m!"{header}{indentD m!"{entry.lhs} =?= {entry.rhs}"}"
  | some ctx =>
    withLCtx ctx.lctx ctx.localInstances do
      let s   := entry.lhs.collectMVars entry.rhs.collectMVars
      /- `p u` is true if it contains a universe metavariable in `s` -/
      let p (u : Level) := u.any fun | Level.mvar m _ => s.contains m | _ => false
      let lhs := exposeRelevantUniverses (← instantiateMVars ctx.lhs) p
      let rhs := exposeRelevantUniverses (← instantiateMVars ctx.rhs) p
      try
        addMessageContext m!"{header}{indentD m!"{entry.lhs} =?= {entry.rhs}"}\nwhile trying to unify{indentD m!"{lhs} : {← inferType lhs}"}\nwith{indentD m!"{rhs} : {← inferType rhs}"}"
      catch _ =>
        addMessageContext m!"{header}{indentD m!"{entry.lhs} =?= {entry.rhs}"}\nwhile trying to unify{indentD lhs}\nwith{indentD rhs}"

def mkLevelStuckErrorMessage (entry : PostponedEntry) : MetaM MessageData := do
  mkLeveErrorMessageCore "stuck at solving universe constraint" entry

def mkLevelErrorMessage (entry : PostponedEntry) : MetaM MessageData := do
  mkLeveErrorMessageCore "failed to solve universe constraint" entry

private def processPostponedStep (exceptionOnFailure : Bool) : MetaM Bool :=
  traceCtx `Meta.isLevelDefEq.postponed.step do
    let ps ← getResetPostponed
    for p in ps do
      unless (← withReader (fun ctx => { ctx with defEqCtx? := p.ctx? }) <| isLevelDefEqAux p.lhs p.rhs) do
        if exceptionOnFailure then
          throwError (← mkLevelErrorMessage p)
        else
          return false
    return true

partial def processPostponed (mayPostpone : Bool := true) (exceptionOnFailure := false) : MetaM Bool := do
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
          if !(← processPostponedStep exceptionOnFailure) then
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

/--
  `checkpointDefEq x` executes `x` and process all postponed universe level constraints produced by `x`.
  We keep the modifications only if `processPostponed` return true and `x` returned `true`.

  If `mayPostpone == false`, all new postponed universe level constraints must be solved before returning.
  We currently try to postpone universe constraints as much as possible, even when by postponing them we
  are not sure whether `x` really succeeded or not.
-/
@[specialize] def checkpointDefEq (x : MetaM Bool) (mayPostpone : Bool := true) : MetaM Bool := do
  let s ← saveState
  let postponed ← getResetPostponed
  try
    if (← x) then
      if (← processPostponed mayPostpone) then
        let newPostponed ← getPostponed
        setPostponed (postponed ++ newPostponed)
        return true
      else
        s.restore
        return false
    else
      s.restore
      return false
  catch ex =>
    s.restore
    throw ex

def isLevelDefEq (u v : Level) : MetaM Bool :=
  traceCtx `Meta.isLevelDefEq do
    let b ← checkpointDefEq (mayPostpone := true) <| Meta.isLevelDefEqAux u v
    trace[Meta.isLevelDefEq] "{u} =?= {v} ... {if b then "success" else "failure"}"
    return b

def isExprDefEq (t s : Expr) : MetaM Bool :=
  traceCtx `Meta.isDefEq <| withReader (fun ctx => { ctx with defEqCtx? := some { lhs := t, rhs := s, lctx := ctx.lctx, localInstances := ctx.localInstances } }) do
    let b ← checkpointDefEq (mayPostpone := true) <| Meta.isExprDefEqAux t s
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
