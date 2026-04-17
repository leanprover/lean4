/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Util.CollectMVars
public import Lean.Meta.DecLevel
public import Lean.Meta.HasAssignableMVar

public section

namespace Lean.Meta

/--
  Return true iff `lvl` occurs in `max u_1 ... u_n` and `lvl != u_i` for all `i in [1, n]`.
  That is, `lvl` is a proper level subterm of some `u_i`. -/
private def strictOccursMax (lvl : Level) : Level → Bool
  | Level.max u v => visit u || visit v
  | _             => false
where
  visit : Level → Bool
    | Level.max u v => visit u || visit v
    | u             => u != lvl && lvl.occurs u

/-- `mkMaxArgsDiff mvarId (max u_1 ... (mvar mvarId) ... u_n) v` => `max u_1 ... u_n v` -/
private def mkMaxArgsDiff (mvarId : LMVarId) : Level → Level → Level
  | Level.max u v,     acc => mkMaxArgsDiff mvarId u <| mkMaxArgsDiff mvarId v acc
  | l@(Level.mvar id), acc => if id == mvarId then acc else mkLevelMax' l acc
  | l,                 acc => mkLevelMax' l acc

/--
(SelfMax) Solves `?m =?= max ?m v` by creating a fresh metavariable `?n`
and assigning `?m := max ?n v`. (The constraint `v ≤ ?m` is being represented using `max`.)

This rule can make other unification problems become stuck, and it can depend on the
unification order. For example, given the equations
  `?m =?= max ?m ?u`, `?m =?= v`, `?u =?= v`
if we apply SelfMax first and assign `?m := max ?n ?u`, then the second equation
becomes `max ?n ?u =?= v`, which becomes `max ?n v =?= v` after the third equation,
which is stuck. If instead we assigned `?m := v` first, then the first equation
becomes `v =?= max v ?u`, which is stuck, but then the third equation unsticks it by solving it.

We defer applying this rule until we are processing postponed constraints.

The approximations in `trySolveApprox` are heuristics to fix this non-confluence.
-/
private def solveSelfMax (mvarId : LMVarId) (v : Level) : MetaM LBool := do
  if (← read).univApprox ≥ 1 then
    assert! v.isMax
    let n ← mkFreshLevelMVar
    let v' := mkMaxArgsDiff mvarId v n
    trace[Meta.isLevelDefEq.step] "SelfMax: {mkLevelMVar mvarId} := {v'}"
    assignLevelMVar mvarId v'
    return LBool.true
  else
    return LBool.undef

/--
`splitMaxArgs (max u₁ ... uₘ) (max v₁ ... vₙ)` returns `(s, u', v')`,
where `s` is the max of the shared components, `u'` is the max of the components unique to `u`,
and `v'` is the max of the components unique to `v`.
The result satisfies `u = max s u'` and `v = max s v'`, up to reordering and reassociating.
Assumes `u` and `v` are normalized (components are in sorted order and `max` is right-associated).
-/
private partial def splitMaxArgs (u v : Level) : Level × Level × Level :=
  match u, v with
  | u,           .zero       => (.zero, u, .zero)
  | .zero,       v           => (.zero, .zero, v)
  | .max u₁ u₂,  .max v₁ v₂  => step u₁ u₂ v₁ v₂
  | .max u₁ u₂,  v           => step u₁ u₂ v .zero
  | u,           .max v₁ v₂  => step u .zero v₁ v₂
  | u,           v           => step u .zero v .zero
where
  step (u₁ u₂ v₁ v₂ : Level) : Level × Level × Level :=
    if u₁ == v₁ then
      let (s, u', v') := splitMaxArgs u₂ v₂
      (mkLevelMax' u₁ s, u', v')
    else if Level.normLt u₁ v₁ then
      let (s, u', v') := splitMaxArgs u₂ v
      (s, mkLevelMax' u₁ u', v')
    else
      let (s, u', v') := splitMaxArgs u v₂
      (s, u', mkLevelMax' v₁ v')

-- private def isMaxOfMVars? : Level → (acc : Array LMVarId := #[]) → Option (Array LMVarId)
--   | .mvar mvarId, acc => acc.push mvarId
--   | .max u v,     acc => isMaxOfMVars? u acc |>.bind (isMaxOfMVars? v ·)
--   | _,            _   => none

private def isAllDecOrMVar? : Level → (acc : Array Level := #[]) → Option (Array Level)
  | .max u v,     acc => isAllDecOrMVar? u acc |>.bind (isAllDecOrMVar? v ·)
  | u,            acc =>
    if u.isMVar then
      acc.push u
    else if let some u' := u.dec then
      acc.push (Level.succ u')
    else
      none

/--
Tries applying an approximation to solve for metavariables, returning `true` on success.

The docstring at `solveSelfMax` gives an example of how unification can become stuck
depending on the order of unification. The approximations here attempt to analyze

Approximations:
- SelfMax: If `v` is of the form `max u ?m` then solves `u =?= max u ?m` by assigning `?m := u`.
  Note that `u` can be a `max` expression.
  This is an approximation. For example, we ignore the solution `?m := 0`.
- MaxMax: If `u` is of the form `max u₁ u₂` and `v` is of the form `max u₁ ?m`
  then solves `max u₁ u₂ =?= max u₁ ?m` by assigning `?m := u₂`.
  Note that `u₁` can be a `max` expression.
  This is an approximation. For example, we ignore the solution `?w := max u₁ u₂`.
- SuccMax: If `u` is of the form `u'+1` and `v` is of the form `max v₁ … vₙ` such that
  each `vᵢ` is a metavariable `?mᵢ` or the successor of some level `vᵢ'`, then assign `?mᵢ := ?mᵢ'+1`
  for fresh level metavariables `?mᵢ`.

-- TODO: investigate whether we need to improve these approximations.
-/
private def trySolveApprox (u v : Level) : MetaM Bool := do
  if !v.isMax then
    -- All approximations are for the case when `v` is a `max` expression.
    return false
  let (s, u', v') := splitMaxArgs u v
  if let .mvar mvarId := v' then
    assert! !s.isZero
    if (← mvarId.isReadOnly) then
      return false
    else if v'.occurs u then
      return false
    else if u'.isZero then
      -- Thus `u = s` so `v = max u ?m`.
      -- The SelfMax approximation applies.
      trace[Meta.isLevelDefEq.step] "SelfMax approximation: {mkLevelMVar mvarId} := {u}"
      assignLevelMVar mvarId u
      return true
    else
      -- Thus `u = max s u'` and `v = max s ?m`, with `s ≠ 0` and `u' ≠ 0`.
      -- The MaxMax approximation applies.
      trace[Meta.isLevelDefEq.step] "MaxMax approximation: {mkLevelMVar mvarId} := {u'}"
      assignLevelMVar mvarId u'
      return true
  else
    if let Level.succ u' := u then
      if let some args := isAllDecOrMVar? v then
        let u'' := u'.getLevelOffset
        if !u''.isMVar || !args.any (· == u'') then
          if !(← (args |>.filter (fun arg => arg.isMVar) |>.anyM fun mvar => mvar.mvarId!.isReadOnly)) then
            trace[Meta.isLevelDefEq.step] "SuccMax approximation"
            let args ← args.mapM Meta.decLevel
            return ← isLevelDefEqAux u' (Level.mkNaryMax args.toList)
    return false

private def postponeIsLevelDefEq (lhs : Level) (rhs : Level) : MetaM Unit := do
  let ref ← getRef
  let ctx ← read
  trace[Meta.isLevelDefEq.stuck] "{lhs} =?= {rhs}"
  modifyPostponed fun postponed => postponed.push { lhs := lhs, rhs := rhs, ref := ref, ctx? := ctx.defEqCtx? }

private def isMVarWithGreaterDepth (v : Level) (mvarId : LMVarId) : MetaM Bool :=
  match v with
  | Level.mvar mvarId' => return (← mvarId'.getLevel) > (← mvarId.getLevel)
  | _ => return false

/--
Decrements both `lhs` and `rhs` so long as they are both successors.
Skips calling `k` if `lhs.getLevelOffset == rhs.getLevelOffset`,
or if `lhs` or `rhs` is a successor and the other cannot be a successor for any metavariable assignment.
Instantiates metavariables and normalizes.
-/
@[specialize] private partial def isLevelDefEqPreprocess (lhs rhs : Level) (k : Level → Level → MetaM Bool) (instantiated : Bool := false) (trace : Bool := false) : MetaM Bool := do
  match lhs.dec, rhs.dec with
  | some lhs', some rhs' => isLevelDefEqPreprocess lhs' rhs' k instantiated (trace := true)
  | _, _ =>
    if lhs.getLevelOffset == rhs.getLevelOffset then
      return lhs.getOffset == rhs.getOffset
    else if !instantiated then
      let lhs' ← instantiateLevelMVars lhs
      let rhs' ← instantiateLevelMVars rhs
      isLevelDefEqPreprocess lhs' rhs' k (instantiated := true) (trace := trace)
    else if !lhs.isNormalized || !rhs.isNormalized then
      let lhs' := lhs.normalize
      let rhs' := rhs.normalize
      return ← isLevelDefEqPreprocess lhs' rhs' k (instantiated := true) (trace := true)
    else
      if trace then
        withTraceNodeBefore (collapsed := false) `Meta.isLevelDefEq (fun _ => return m!"simplified: {lhs} =?= {rhs}") do
          k lhs rhs
      else
        k lhs rhs

@[specialize] private def withFlipped (solve : Level → Level → MetaM LBool) (lhs rhs : Level) (k : MetaM Bool) : MetaM Bool := do
  let r ← solve lhs rhs
  if r != LBool.undef then
    return r == LBool.true
  else
    let r ← solve rhs lhs
    if r != LBool.undef then
      return r == LBool.true
    else
      k

set_option compiler.ignoreBorrowAnnotation true in
mutual

  private partial def solve (u v : Level) : MetaM LBool := do
    match u, v with
    | Level.mvar mvarId, _ =>
      if (← mvarId.isReadOnly) then
        return LBool.undef
      else if (← isMVarWithGreaterDepth v mvarId) then
        -- If both `u` and `v` are both metavariables, but depth of v is greater, then we assign `v := u`.
        -- This can only happen when levelAssignDepth is set to a smaller value than depth (e.g. during TC synthesis)
        trace[Meta.isLevelDefEq.step] "{v} := {u}"
        assignLevelMVar v.mvarId! u
        return LBool.true
      else if !u.occurs v then
        trace[Meta.isLevelDefEq.step] "{u} := {v}"
        assignLevelMVar u.mvarId! v
        return LBool.true
      else if v.isMax && !strictOccursMax u v then
        solveSelfMax u.mvarId! v
      else
        return LBool.undef
    | _, Level.mvar .. => return LBool.undef -- Let `solve v u` handle this case
    | Level.zero, Level.max v₁ v₂ =>
      Bool.toLBool <$> (isLevelDefEqAuxImpl Level.zero v₁ <&&> isLevelDefEqAuxImpl Level.zero v₂)
    | Level.zero, Level.imax _ v₂ =>
      Bool.toLBool <$> isLevelDefEqAuxImpl Level.zero v₂
    | Level.zero, Level.succ .. => return LBool.false
    | Level.succ .., Level.param .. => return LBool.false
    | _, _ =>
      match v with
      | .imax v₁ v₂ =>
        if (← read).univApprox ≥ 1 then
          if u.dec.isSome then
            /-
            `u'+1 =?= imax (v₁'+1) v₂` implies `1 ≤ v₂`.
            For this to be true, it must be that there exists some `v₂'` such that `v₂ =?= max v₂' 1`.
            Just like for `solveSelfMax`, we only do this once we're processing postponed constraints,
            since `max` unification can cause other unification problems to become stuck.
            -/
            let v₂' ← mkFreshLevelMVar
            return ← Bool.toLBool <$> (isLevelDefEqAuxImpl v₂ (Level.max 1 v₂') <&&> isLevelDefEqAuxImpl u (Level.max v₁ v₂))
      | _ => pure ()
      return LBool.undef

  partial def solveApprox (u v : Level) : MetaM LBool := do
    if (← read).univApprox ≥ 2 then
      if ← trySolveApprox u v then
        return LBool.true
    return LBool.undef

  @[export lean_is_level_def_eq]
  partial def isLevelDefEqAuxImpl (lhs rhs : Level) : MetaM Bool := withIncRecDepth do
    withTraceNodeBefore `Meta.isLevelDefEq
        (fun _ => do
          let mut pre := []
          if (← read).univApprox > 0 then pre := m!"approx {(← read).univApprox}" :: pre
          if (← read).univProcessingPostponed then pre := m!"in postponed" :: pre
          let msg := if pre.isEmpty then m!"" else m!"[{MessageData.joinSep pre ", "}] "
          return m!"{msg}{lhs} =?= {rhs}") do
      isLevelDefEqPreprocess lhs rhs fun lhs rhs => do
        if !(← hasAssignableLevelMVar lhs <||> hasAssignableLevelMVar rhs) then
          let cfg ← getConfig
          if cfg.isDefEqStuckEx && (lhs.isMVar || rhs.isMVar) then do
            trace[Meta.isLevelDefEq.stuck] "{lhs} =?= {rhs}"
            Meta.throwIsDefEqStuck
          else
            return false
        else
          withFlipped solve lhs rhs do
            withFlipped solveApprox lhs rhs do
              postponeIsLevelDefEq lhs rhs
              return true
end

builtin_initialize
  registerTraceClass `Meta.isLevelDefEq
  registerTraceClass `Meta.isLevelDefEq.stuck (inherited := true)

end Lean.Meta
