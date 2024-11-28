/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Elab.PreDefinition.MkInhabitant
import Lean.Elab.PreDefinition.WF.PackMutual
import Init.Tailrec

namespace Lean.Elab
open WF
open Meta

partial def solveMono (goal : MVarId) : MetaM Unit := goal.withContext do
  trace[Elab.definition.tailrec] "solveMono at\n{goal}"
  let type ← goal.getType
  if type.isForall then
    let (_, goal) ← goal.intro1P
    solveMono goal
    return

  let_expr Tailrec.mono α β γ inst₁ inst₂ f := type |
    throwError "Unexpected goal:\n{goal}"

  unless f.isLambda do
    throwError "Unexpected goal:\n{goal}"

  let failK :=
    lambdaBoundedTelescope f 1 fun _ t => do
      trace[Elab.definition.tailrec] "Failing at goal\n{goal}"
      throwError "Recursive call in non-tail position:{indentExpr t}"

  let e := f.bindingBody!

  -- No recursive calls left
  if !e.hasLooseBVars then
    -- should not use applyConst here; it may try to re-synth the Nonempty constriant
    let us := type.getAppFn.constLevels!
    let p := mkAppN (.const ``Tailrec.mono_const us) #[α, β, γ, inst₁, inst₂, e]
    let new_goals ←
      mapError (f := (m!"Could not apply {p}:{indentD ·}}")) do
        goal.apply p
    unless new_goals.isEmpty do
      throwError "Left over goals"
    return

  -- NB: `e` is now an open term.

  -- A recursive call directly here
  if e.isApp && e.appFn! == .bvar 0 then
    -- should not use applyConst here; it may try to re-synth the Nonempty constriant
    let x := e.appArg!
    let us := type.getAppFn.constLevels!.take 2
    let p := mkAppN (.const ``Tailrec.mono_apply us) #[α, β, inst₁, x]
    let new_goals ←
      mapError (f := (m!"Could not apply {p}:{indentD ·}}")) do
        goal.apply p
    unless new_goals.isEmpty do
      throwError "Left over goals"
    return

  -- Float letE to the environment
  if let .letE n t v b _nonDep := e then
    if t.hasLooseBVars || v.hasLooseBVars then
      failK
    withLetDecl n t v fun x => do
      let b' := f.updateLambdaE! f.bindingDomain! (b.instantiate1 x)
      let goal' ← mkFreshExprSyntheticOpaqueMVar (mkApp type.appFn! b')
      goal.assign (← mkLetFVars #[x] goal')
      solveMono goal'.mvarId!
    return

  -- Manually handle PSigma.casesOn, and PSum.casesOn, as split doesn't
  -- and we need it due to the way we pack mutual arguments
  -- and while we are at it, handle ite and dite as well.
  -- Feels more reliable and predictable than splitting
  match_expr e with
  | PSigma.casesOn δ ε γ p k =>
    if e.appFn!.hasLooseBVars then
      failK
    -- Careful juggling of universes
    let us := type.getAppFn.constLevels! ++ e.getAppFn.constLevels!.tail
    let k' := f.updateLambdaE! f.bindingDomain! k
    let p := mkApp9 (.const ``Tailrec.mono_psigma_casesOn us) α β inst₁ δ ε γ p inst₂ k'
    check p
    let new_goals ←
      mapError (f := (m!"Could not apply {p}:{indentD ·}}")) do
        goal.apply p
    new_goals.forM solveMono
    return
  | PSum.casesOn δ ε γ p k₁ k₂ =>
    if e.appFn!.appFn!.hasLooseBVars then
      failK
    -- Careful juggling of universes
    let us := type.getAppFn.constLevels! ++ e.getAppFn.constLevels!.tail
    let k₁' := f.updateLambdaE! f.bindingDomain! k₁
    let k₂' := f.updateLambdaE! f.bindingDomain! k₂
    let p := mkAppN (.const ``Tailrec.mono_psum_casesOn us) #[α, β, inst₁, δ, ε, γ, p, inst₂, k₁', k₂']
    check p
    let new_goals ←
      mapError (f := (m!"Could not apply {p}:{indentD ·}}")) do
        goal.apply p
    new_goals.forM solveMono
    return
   | ite _ cond decInst k₁ k₂ =>
    let us := type.getAppFn.constLevels!
    let k₁' := f.updateLambdaE! f.bindingDomain! k₁
    let k₂' := f.updateLambdaE! f.bindingDomain! k₂
    let p := mkAppN (.const ``Tailrec.mono_ite us) #[α, β, γ, inst₁, inst₂, cond, decInst, k₁', k₂']
    check p
    let new_goals ←
      mapError (f := (m!"Could not apply {p}:{indentD ·}}")) do
        goal.apply p
    new_goals.forM solveMono
    return
   | dite _ cond decInst k₁ k₂ =>
    let us := type.getAppFn.constLevels!
    let k₁' := f.updateLambdaE! f.bindingDomain! k₁
    let k₂' := f.updateLambdaE! f.bindingDomain! k₂
    let p := mkAppN (.const ``Tailrec.mono_dite us) #[α, β, γ, inst₁, inst₂, cond, decInst, k₁', k₂']
    check p
    let new_goals ←
      mapError (f := (m!"Could not apply {p}:{indentD ·}}")) do
        goal.apply p
    new_goals.forM solveMono
    return
  | _ => pure

  -- We could be even more deliberate here and use the `lifter` lemmas
  -- for the match statements instead of the `split` tactic.
  -- For now using `splitMatch` works fine.
  if Lean.Meta.Split.findSplit?.isCandidate (← getEnv) (e := e) (splitIte := false) then
    let new_goals ← Split.splitMatch goal e
    new_goals.forM solveMono
    return

  failK

private def replaceRecApps (recFnName : Name) (fixedPrefixSize : Nat) (F : Expr) (e : Expr) : Expr :=
  e.replace fun e =>
    if e.isAppOfArity recFnName fixedPrefixSize then
      some F
    else
      none

def derecursifyTailrec (fixedPrefixSize : Nat) (preDef : PreDefinition) (w : Expr) :
    TermElabM PreDefinition := do
  -- TODO: Witness and fixed prefix
  forallBoundedTelescope preDef.type fixedPrefixSize fun prefixArgs type => do
    let w := mkAppN w prefixArgs
    let type ← whnfForall type
    unless type.isForall do
      throwError "expected unary function type: {type}"
    let α := type.bindingDomain!

    let F ← withoutModifyingEnv do
      addAsAxiom preDef
      let value ←
        withLocalDeclD `F type fun f =>
          withLocalDeclD `x α fun x => do
            let val := preDef.value.beta (prefixArgs.push x)
            let val := replaceRecApps preDef.declName prefixArgs.size f val
            mkLambdaFVars #[f, x] val
      eraseRecAppSyntaxExpr value

    let inst ← withLocalDeclD `x α fun x => do
      mkLambdaFVars #[x] (← mkAppM ``Nonempty.intro #[.app w x])
    let value ← mkAppOptM ``Lean.Tailrec.tailrec_fix #[α, none, inst, F]

    -- Now try to prove the monotonicity
    let monoGoal := (← inferType value).bindingDomain!
    let mono ← mkFreshExprSyntheticOpaqueMVar monoGoal
    mapError (f := (m!"Could not prove function to be tailrecursive:{indentD ·}")) do
      solveMono mono.mvarId!
    let value := .app value (← instantiateMVars mono)

    let value ← mkLambdaFVars prefixArgs value
    return { preDef with value }

def tailRecursion (preDefs : Array PreDefinition) : TermElabM Unit := do
  let witnesses ← preDefs.mapM fun preDef =>
    let msg := m!"failed to compile definition '{preDef.declName}' via tailrecursion"
    mkInhabitantFor msg #[] preDef.type

  trace[Elab.definition.tailrec] "Found nonempty witnesses: {witnesses}"
  let (fixedPrefixSize, argsPacker, unaryPreDef) ← mkUnaryPreDef preDefs

  -- Apply the same unary/mutual packing to the witnesses.
  let unaryWitness ←
    forallBoundedTelescope unaryPreDef.type fixedPrefixSize fun prefixArgs _ => do
      mkLambdaFVars prefixArgs (← argsPacker.uncurry (witnesses.map (mkAppN · prefixArgs)))

  unless argsPacker.onlyOneUnary do
    trace[Elab.definition.tailrec] "Packed witness:{indentExpr unaryWitness}"

  let preDefNonRec ← derecursifyTailrec fixedPrefixSize unaryPreDef unaryWitness
  addPreDefsFromUnary preDefs fixedPrefixSize argsPacker preDefNonRec (hasInduct := false)

end Lean.Elab

builtin_initialize Lean.registerTraceClass `Elab.definition.tailrec
