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

/--
Registers a monotonicity theorem for `partial_fixpoint`.

Monotonicity theorems should have `Lean.Order.monotone ...` as a conclusion. They are used in the
`monotonicity` tactic (scoped in the `Lean.Order` namespace) to automatically prove monotonicity
for functions defined using `partial_fixpoint`.
-/
@[builtin_doc]
builtin_initialize registerBuiltinAttribute {
  name := `partial_fixpoint_monotone
  descr := "monotonicity theorem"
  add := fun decl _ kind => MetaM.run' do
    let declTy := (← getConstInfo decl).type
    let (xs, _, targetTy) ← withReducible <| forallMetaTelescopeReducing declTy
    let_expr monotone α inst_α β inst_β f := targetTy |
      throwError "@[partial_fixpoint_monotone] attribute only applies to lemmas proving {.ofConstName ``monotone}"
    let f := f.headBeta
    let f ← if f.isLambda then pure f else etaExpand f
    let f := headBetaUnderLambda f
    lambdaBoundedTelescope f 1 fun _ e => do
      let key ← withReducible <| DiscrTree.mkPath e
      monotoneExt.add (decl, key) kind
}

/--
Finds tagged monotonicity theorems of the form `monotone (fun x => e)`.
-/
def findMonoThms (e : Expr) : MetaM (Array Name) := do
  (monotoneExt.getState (← getEnv)).getMatch e

private def defaultFailK (f : Expr) (monoThms : Array Name) : MetaM α :=
  let extraMsg := if monoThms.isEmpty then m!"" else
    m!"Tried to apply {.andList (monoThms.toList.map (m!"'{·}'"))}, but failed."
  throwError "Failed to prove monotonicity of:{indentExpr f}\n{extraMsg}"

private def applyConst (goal : MVarId) (name : Name) : MetaM (List MVarId) := do
  prependError m!"Could not apply {.ofConstName name}:" do
    goal.applyConst name (cfg := { synthAssignedInstances := false})

/--
Base case for solveMonoStep: Handles goals of the form
```
monotone (fun f => f.1.2 x y)
```

It's tricky to solve them compositionally from the outside in, so here we construct the proof
from the inside out.
-/
partial def solveMonoCall (α inst_α : Expr) (e : Expr) : MetaM (Option Expr) := do
  if e.isApp && !e.appArg!.hasLooseBVars then
    let some hmono ← solveMonoCall α inst_α e.appFn! | return none
    let hmonoType ← inferType hmono
    let_expr monotone _ _ _ inst _ := hmonoType | throwError "solveMonoCall {e}: unexpected type {hmonoType}"
    let some inst ← whnfUntil inst ``instOrderPi | throwError "solveMonoCall {e}: unexpected instance {inst}"
    let_expr instOrderPi γ δ inst ← inst | throwError "solveMonoCall {e}: whnfUntil failed?{indentExpr inst}"
    return ← mkAppOptM ``monotone_apply #[γ, δ, α, inst_α, inst, e.appArg!, none, hmono]

  if e.isProj then
    let some hmono ← solveMonoCall α inst_α e.projExpr! | return none
    let hmonoType ← inferType hmono
    let_expr monotone _ _ _ inst _ := hmonoType | throwError "solveMonoCall {e}: unexpected type {hmonoType}"
    let some inst ← whnfUntil inst ``instPartialOrderPProd | throwError "solveMonoCall {e}: unexpected instance {inst}"
    let_expr instPartialOrderPProd β γ inst_β inst_γ ← inst | throwError "solveMonoCall {e}: whnfUntil failed?{indentExpr inst}"
    let n := if e.projIdx! == 0 then ``PProd.monotone_fst else ``PProd.monotone_snd
    return ← mkAppOptM n #[β, γ, α, inst_β, inst_γ, inst_α, none, hmono]

  if e == .bvar 0 then
    let hmono ← mkAppOptM ``monotone_id #[α, inst_α]
    return some hmono

  return none


def solveMonoStep (failK : ∀ {α}, Expr → Array Name → MetaM α := @defaultFailK) (goal : MVarId) : MetaM (List MVarId) :=
  goal.withContext do
  trace[Elab.Tactic.monotonicity] "monotonicity at\n{goal}"
  let type ← goal.getType
  if type.isForall then
    let (_, goal) ← goal.intro1P
    return [goal]

  match_expr type with
  | monotone α inst_α β inst_β f =>
    -- Ensure f is not headed by a redex and headed by at least one lambda, and clean some
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

    -- Look through mdata
    if e.isMData then
      let f' := f.updateLambdaE! f.bindingDomain! e.mdataExpr!
      let goal' ← mkFreshExprSyntheticOpaqueMVar (mkApp type.appFn! f')
      goal.assign goal'
      return [goal'.mvarId!]

    -- Handle let
    if let .letE n t v b _nonDep := e then
      if t.hasLooseBVars || v.hasLooseBVars then
        -- We cannot float the let to the context, so just zeta-reduce.
        let b' := f.updateLambdaE! f.bindingDomain! (b.instantiate1 v)
        let goal' ← mkFreshExprSyntheticOpaqueMVar (mkApp type.appFn! b')
        goal.assign goal'
        return [goal'.mvarId!]
      else
        -- No recursive call in t or v, so float out
        let goal' ← withLetDecl n t v fun x => do
          let b' := f.updateLambdaE! f.bindingDomain! (b.instantiate1 x)
          let goal' ← mkFreshExprSyntheticOpaqueMVar (mkApp type.appFn! b')
          goal.assign (← mkLetFVars #[x] goal')
          pure goal'
        return [goal'.mvarId!]

    -- Float `letFun` to the environment.
    -- (cannot use `applyConst`, it tends to reduce the let redex)
    match_expr e with
    | letFun γ _ v b =>
      if γ.hasLooseBVars || v.hasLooseBVars then
        failK f #[]
      let b' := f.updateLambdaE! f.bindingDomain! b
      let p  ← mkAppOptM ``monotone_letFun #[α, β, γ, inst_α, inst_β, v, b']
      let new_goals ← prependError m!"Could not apply {p}:" do
        goal.apply p
      let [new_goal] := new_goals
          | throwError "Unexpected number of goals after {.ofConstName ``monotone_letFun}."
      let (_, new_goal) ←
        if b.isLambda then
          new_goal.intro b.bindingName!
        else
          new_goal.intro1
      return [new_goal]
    | _ => pure ()

    -- Handle lambdas, preserving the name of the binder
    if e.isLambda then
      let [new_goal] ← applyConst goal ``monotone_of_monotone_apply
        | throwError "Unexpected number of goals after {.ofConstName ``monotone_of_monotone_apply}."
      let (_, new_goal) ← new_goal.intro e.bindingName!
      return [new_goal]

    -- A recursive call directly here
    if e.isBVar then
      return ← applyConst goal ``monotone_id

    -- A recursive call
    if let some hmono ← solveMonoCall α inst_α e then
      trace[Elab.Tactic.monotonicity] "Found recursive call {e}:{indentExpr hmono}"
      unless ← goal.checkedAssign hmono do
        trace[Elab.Tactic.monotonicity] "Failed to assign {hmono} : {← inferType hmono} to goal"
        failK f #[]
      return []

    let monoThms ← withLocalDeclD `f f.bindingDomain! fun f =>
      -- The discrimination tree does not like open terms
      findMonoThms (e.instantiate1 f)
    trace[Elab.Tactic.monotonicity] "Found monoThms: {monoThms.map MessageData.ofConstName}"
    for monoThm in monoThms do
      let new_goals? ← try
        let new_goals ← applyConst goal monoThm
        trace[Elab.Tactic.monotonicity] "Succeeded with {.ofConstName monoThm}"
        pure (some new_goals)
      catch e =>
        trace[Elab.Tactic.monotonicity] "{e.toMessageData}"
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

open Elab Tactic in
@[builtin_tactic Lean.Order.monotonicity]
def evalMonotonicity : Tactic := fun _stx =>
  liftMetaTactic Lean.Meta.Monotonicity.solveMonoStep

end Lean.Meta.Monotonicity

builtin_initialize Lean.registerTraceClass `Elab.Tactic.monotonicity
