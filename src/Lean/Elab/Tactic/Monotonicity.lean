/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
prelude
import Lean.Meta.Tactic.Split
import Lean.Elab.RecAppSyntax
import Lean.Elab.Tactic.Basic
import Init.Internal.Order

namespace Lean.Meta.Monotonicity

open Lean Meta
open Lean.Order

partial def headBetaUnderLambda (f : Expr) : Expr := Id.run do
  let mut f := f.headBeta
  if f.isLambda then
    while f.bindingBody!.isHeadBetaTarget do
      f := f.updateLambda! f.bindingInfo! f.bindingDomain! f.bindingBody!.headBeta
  return f


/-- Environment extensions for monotonicity lemmas -/
builtin_initialize monotoneExt :
    SimpleScopedEnvExtension (Name × Array DiscrTree.Key) (DiscrTree Name) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun dt (n, ks) => dt.insertCore ks n
    initial := {}
  }

builtin_initialize registerBuiltinAttribute {
  name := `partial_monotone
  descr := "monotonicity theorem"
  add := fun decl _ kind => MetaM.run' do
    let declTy := (← getConstInfo decl).type
    let (xs, _, targetTy) ← withReducible <| forallMetaTelescopeReducing declTy
    let_expr monotone α inst_α β inst_β f := targetTy |
      throwError "@[partial_monotone] attribute only applies to lemmas proving {.ofConstName ``monotone}"
    let f := f.headBeta
    let f ← if f.isLambda then pure f else etaExpand f
    let f := headBetaUnderLambda f
    lambdaBoundedTelescope f 1 fun _ e => do
      let key ← withReducible <| DiscrTree.mkPath e
      monotoneExt.add (decl, key) kind
}

/--
Given expression `e` of the form `f xs`, possibly open, try to find monotonicity theorems.
for f.
-/
def findMonoThms (e : Expr) : MetaM (Array Name) := do
  -- The `letFun` theorem does not play well with the discrimination tree
  if e.isLetFun then return #[``monotone_letFun]
  (monotoneExt.getState (← getEnv)).getMatch e

private def defaultFailK (f : Expr) (monoThms : Array Name) : MetaM α :=
  let extraMsg := if monoThms.isEmpty then m!"" else
    m!"Tried to apply {.andList (monoThms.toList.map (m!"'{·}'"))}, but failed."
  throwError "Failed to prove monotonicity of:{indentExpr f}\n{extraMsg}"

private def applyConst (goal : MVarId) (name : Name) : MetaM (List MVarId) := do
  mapError (f := (m!"Could not apply {.ofConstName name}:{indentD ·}")) do
    goal.applyConst name (cfg := { synthAssignedInstances := false})

def solveMonoStep (failK : ∀ {α}, Expr → Array Name → MetaM α := @defaultFailK) (goal : MVarId) : MetaM (List MVarId) :=
  goal.withContext do
  trace[Elab.Tactic.partial_monotonicity] "partial_monotonicity at\n{goal}"
  let type ← goal.getType
  if type.isForall then
    let (_, goal) ← goal.intro1P
    return [goal]

  match_expr type with
  | forall_arg _α _β _γ _P f =>
    let f ← instantiateMVars f
    let f := headBetaUnderLambda f
    if f.isLambda && f.bindingBody!.isLambda then
      let name := f.bindingBody!.bindingName!
      let (_, new_goal) ← goal.intro name
      return [new_goal]
    else
      let (_, new_goal) ← goal.intro1
      return [new_goal]

  | monotone _α _inst_α _β _inst_β f =>
    -- Ensure f is headed not a redex and headed by at least one lambda, and clean some
    -- redexes left by some of the lemmas we tend to apply
    let f ← instantiateMVars f
    let f := f.headBeta
    let f ← if f.isLambda then pure f else etaExpand f
    let f := headBetaUnderLambda f
    let e := f.bindingBody!

    -- No recursive calls left
    if !e.hasLooseBVars then
      return ← applyConst goal ``monotone_const

    -- NB: `e` is now an open term.

    -- A recursive call directly here
    if e.isApp && e.appFn! == .bvar 0 then
      return ← applyConst goal ``monotone_apply

    -- Look through mdata
    if e.isMData then
      let f' := f.updateLambdaE! f.bindingDomain! e.mdataExpr!
      let goal' ← mkFreshExprSyntheticOpaqueMVar (mkApp type.appFn! f')
      goal.assign goal'
      return [goal'.mvarId!]

    -- Float letE to the environment
    if let .letE n t v b _nonDep := e then
      if t.hasLooseBVars || v.hasLooseBVars then
        failK f #[]
      let goal' ← withLetDecl n t v fun x => do
        let b' := f.updateLambdaE! f.bindingDomain! (b.instantiate1 x)
        let goal' ← mkFreshExprSyntheticOpaqueMVar (mkApp type.appFn! b')
        goal.assign (← mkLetFVars #[x] goal')
        pure goal'
      return [goal'.mvarId!]

    let monoThms ← withLocalDeclD `f f.bindingDomain! fun f =>
      -- The discrimination tree does not like open terms
      findMonoThms (e.instantiate1 f)
    trace[Elab.Tactic.partial_monotonicity] "Found monoThms: {monoThms}"
    for monoThm in monoThms do
      let new_goals? ← try
        let new_goals ← applyConst goal monoThm
        trace[Elab.Tactic.partial_monotonicity] "Succeeded with {monoThm}"
        pure (some new_goals)
      catch e =>
        trace[Elab.Tactic.partial_monotonicity] "{e.toMessageData}"
        pure none
      if let some new_goals := new_goals? then
        return new_goals

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
        return ← Split.splitMatch goal e

    failK f monoThms
  | _ =>
    throwError "Unexpected goal:{goal}"

partial def solveMono (failK : ∀ {α}, Expr → Array Name → MetaM α := defaultFailK) (goal : MVarId) : MetaM Unit := do
  let new_goals ← solveMonoStep failK goal
  new_goals.forM (solveMono failK)

end Lean.Meta.Monotonicity


open Lean Elab Tactic in
@[builtin_tactic Lean.Order.monotonicity]
def evalApplyRules : Tactic := fun _stx =>
    liftMetaTactic Lean.Meta.Monotonicity.solveMonoStep

builtin_initialize Lean.registerTraceClass `Elab.Tactic.partial_monotonicity
