/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Util.CollectMVars
import Lean.Meta.Basic
import Lean.Meta.InferType
import Lean.Meta.DecLevel

namespace Lean.Meta

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
    | _, Level.mvar .. => return LBool.undef -- Let `solve v u` to handle this case
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

  @[export lean_is_level_def_eq]
  partial def isLevelDefEqAuxImpl : Level → Level → MetaM Bool
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

builtin_initialize
  registerTraceClass `Meta.isLevelDefEq
  registerTraceClass `Meta.isLevelDefEq.step

end Lean.Meta
