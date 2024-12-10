/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
prelude
import Lean.Meta.Tactic.Split
import Lean.Elab.RecAppSyntax
import Lean.Elab.Tactic.Basic
import Init.Tailrec

namespace Lean.Elab.Monotonicity

open Lean Meta

partial def headBetaUnderLambda (f : Expr) : Expr := Id.run do
  let mut f := f.headBeta
  if f.isLambda then
    while f.bindingBody!.isHeadBetaTarget do
      f := f.updateLambda! f.bindingInfo! f.bindingDomain! f.bindingBody!.headBeta
  return f

/--
Given expression `e` of the form `f xs`, possibly open, try to find monotonicity theorems.
for f.
-/
-- TODO: Replace with extensible attribute
def findMonoThms (e : Expr) : MetaM (Array Name) :=
  match_expr e with
  | ite _ _ _ _ _ =>                pure #[``Tailrec.monotone_ite]
  | dite _ _ _ _ _ =>               pure #[``Tailrec.monotone_dite]
  | letFun _ _ _ _ =>               pure #[``Tailrec.monotone_letFun]
  | Bind.bind _ _ _ _ _ _ =>        pure #[``Tailrec.monotone_bind]
  | List.mapM _ _ _ _ _ _ =>        pure #[``Tailrec.monotone_mapM]
  | Array.mapFinIdxM _ _ _ _ _ _ => pure #[``Tailrec.monotone_mapFinIdxM]
  | _ => pure #[]

private def defaultFailK (f : Expr) (monoThms : Array Name) : MetaM Unit :=
  let extraMsg := if monoThms.isEmpty then m!"" else
    m!"Tried to apply {.andList (monoThms.toList.map (m!"'{·}'"))}, but failed."
  throwError "Failed to prove monotonicity of:{indentExpr f}\n{extraMsg}"

partial def solveMono  (goal : MVarId) (failK : Expr → Array Name → MetaM Unit := defaultFailK) : MetaM Unit := goal.withContext do
  trace[Elab.definition.tailrec] "solveMono at\n{goal}"
  let type ← goal.getType
  if type.isForall then
    let (_, goal) ← goal.intro1P
    solveMono goal failK
    return

  match_expr type with
  | Tailrec.forall_arg _α _β _γ _P f =>
    let f ← instantiateMVars f
    let f := headBetaUnderLambda f
    if f.isLambda && f.bindingBody!.isLambda then
      let name := f.bindingBody!.bindingName!
      let (_, new_goal) ← goal.intro name
      solveMono new_goal failK
    else
      let (_, new_goal) ← goal.intro1
      solveMono new_goal failK

  | Tailrec.monotone α inst_α β inst_β f =>
    -- Ensure f is headed not a redex and headed by at least one lambda, and clean some
    -- redexes left by some of the lemmas we tend to apply
    let f ← instantiateMVars f
    let f := f.headBeta
    let f ← if f.isLambda then pure f else etaExpand f
    let f := headBetaUnderLambda f


    let e := f.bindingBody!

    -- No recursive calls left
    if !e.hasLooseBVars then
      -- should not use applyConst here; it may try to re-synth the Nonempty constriant
      let us := type.getAppFn.constLevels!
      let p := mkAppN (.const ``Tailrec.monotone_const us) #[α, inst_α, β, inst_β, e]
      let new_goals ←
        mapError (f := (m!"Could not apply {p}:{indentD ·}}")) do
          goal.apply p
      unless new_goals.isEmpty do
        throwError "Left over goals"
      return

    -- NB: `e` is now an open term.

    -- A recursive call directly here
    if e.isApp && e.appFn! == .bvar 0 then

      if let some inst_α ← whnfUntil inst_α ``Tailrec.instOrderPi then
        let_expr Tailrec.instOrderPi γ δ inst := inst_α | pure ()
        -- should not use applyConst here; it may try to re-synth the Nonempty constriant
        let x := e.appArg!
        let us := inst_α.getAppFn.constLevels!
        let p := mkAppN (.const ``Tailrec.monotone_apply us) #[γ, δ, inst, x]
        let new_goals ←
          mapError (f := (m!"Could not apply {p}:{indentD ·}}")) do
            goal.apply p
        unless new_goals.isEmpty do
          throwError "Left over goals"
        return

      trace[Elab.definition.tailrec] "Unexpected pi instance:{indentExpr inst_α}"
      failK f #[]

    -- Look through mdata
    if e.isMData then
      let f' := f.updateLambdaE! f.bindingDomain! e.mdataExpr!
      let goal' ← mkFreshExprSyntheticOpaqueMVar (mkApp type.appFn! f')
      goal.assign goal'
      solveMono goal'.mvarId! failK
      return

    -- Float letE to the environment
    if let .letE n t v b _nonDep := e then
      if t.hasLooseBVars || v.hasLooseBVars then
        failK f #[]
      withLetDecl n t v fun x => do
        let b' := f.updateLambdaE! f.bindingDomain! (b.instantiate1 x)
        let goal' ← mkFreshExprSyntheticOpaqueMVar (mkApp type.appFn! b')
        goal.assign (← mkLetFVars #[x] goal')
        solveMono goal'.mvarId! failK
      return

    let monoThms ← findMonoThms e
    for monoThm in monoThms do
      let new_goals? ← try
        some <$> goal.applyConst monoThm (cfg := { synthAssignedInstances := false})
      catch _ =>
        pure none
      if let some new_goals := new_goals? then
        new_goals.forM (solveMono · failK)
        return

    -- Split match-expressions
    if let some info := isMatcherAppCore? (← getEnv) e then
      let candidate ← id do
        let args := e.getAppArgs
        for i in [info.getFirstDiscrPos : info.getFirstDiscrPos + info.numDiscrs] do
          if args[i]!.hasLooseBVars then
            return false
        return true
      if candidate then
        -- We could be even more deliberate here and use the `lifter` lemmas
        -- for the match statements instead of the `split` tactic.
        -- For now using `splitMatch` works fine.
        let new_goals ← Split.splitMatch goal e
        new_goals.forM (solveMono · failK)
        return

    failK f monoThms
  | _ =>
    throwError "Unexpected goal:{goal}"


open Lean.Elab.Tactic

@[builtin_tactic Lean.Parser.Tactic.partialMonotonicity]
def evalApplyRules : Tactic := fun _stx =>
    liftMetaTactic fun g => do
      solveMono g
      pure []
