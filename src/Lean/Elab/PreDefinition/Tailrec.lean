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

/--
For pretty error messages:
Takes `fun f => e`, where `f` is the packed function, and replaces `f` in `e` with the user-visible
constants, which are added to the environment temporarily.
-/
abbrev Unreplacer := Expr → (Expr → MetaM Unit) → MetaM Unit

partial def solveMono (ur : Unreplacer) (goal : MVarId) : MetaM Unit := goal.withContext do
  trace[Elab.definition.tailrec] "solveMono at\n{goal}"
  let type ← goal.getType
  if type.isForall then
    let (_, goal) ← goal.intro1P
    solveMono ur goal
    return

  let_expr Tailrec.mono α β γ inst₁ inst₂ f := type |
    throwError "Unexpected goal:\n{goal}"

  unless f.isLambda do
    throwError "Unexpected goal:\n{goal}"

  let failK := do
    trace[Elab.definition.tailrec] "Failing at goal\n{goal}"
    ur f fun t =>
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

  -- Look through mdata
  if e.isMData then
    let f' := f.updateLambdaE! f.bindingDomain! e.mdataExpr!
    let goal' ← mkFreshExprSyntheticOpaqueMVar (mkApp type.appFn! f')
    goal.assign goal'
    solveMono ur goal'.mvarId!
    return

  -- Float letE to the environment
  if let .letE n t v b _nonDep := e then
    if t.hasLooseBVars || v.hasLooseBVars then
      failK
    withLetDecl n t v fun x => do
      let b' := f.updateLambdaE! f.bindingDomain! (b.instantiate1 x)
      let goal' ← mkFreshExprSyntheticOpaqueMVar (mkApp type.appFn! b')
      goal.assign (← mkLetFVars #[x] goal')
      solveMono ur goal'.mvarId!
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
    let new_goals ←
      mapError (f := (m!"Could not apply {p}:{indentD ·}}")) do
        goal.apply p
    new_goals.forM (solveMono ur)
    return
  | PSum.casesOn δ ε γ p k₁ k₂ =>
    if e.appFn!.appFn!.hasLooseBVars then
      failK
    -- Careful juggling of universes
    let us := type.getAppFn.constLevels! ++ e.getAppFn.constLevels!.tail
    let k₁' := f.updateLambdaE! f.bindingDomain! k₁
    let k₂' := f.updateLambdaE! f.bindingDomain! k₂
    let p := mkAppN (.const ``Tailrec.mono_psum_casesOn us) #[α, β, inst₁, δ, ε, γ, p, inst₂, k₁', k₂']
    let new_goals ←
      mapError (f := (m!"Could not apply {p}:{indentD ·}}")) do
        goal.apply p
    new_goals.forM (solveMono ur)
    return
   | ite _ cond decInst k₁ k₂ =>
    let us := type.getAppFn.constLevels!
    let k₁' := f.updateLambdaE! f.bindingDomain! k₁
    let k₂' := f.updateLambdaE! f.bindingDomain! k₂
    let p := mkAppN (.const ``Tailrec.mono_ite us) #[α, β, γ, inst₁, inst₂, cond, decInst, k₁', k₂']
    let new_goals ←
      mapError (f := (m!"Could not apply {p}:{indentD ·}}")) do
        goal.apply p
    new_goals.forM (solveMono ur)
    return
   | dite _ cond decInst k₁ k₂ =>
    let us := type.getAppFn.constLevels!
    let k₁' := f.updateLambdaE! f.bindingDomain! k₁
    let k₂' := f.updateLambdaE! f.bindingDomain! k₂
    let p := mkAppN (.const ``Tailrec.mono_dite us) #[α, β, γ, inst₁, inst₂, cond, decInst, k₁', k₂']
    let new_goals ←
      mapError (f := (m!"Could not apply {p}:{indentD ·}}")) do
        goal.apply p
    new_goals.forM (solveMono ur)
    return
  | _ => pure

  -- We could be even more deliberate here and use the `lifter` lemmas
  -- for the match statements instead of the `split` tactic.
  -- For now using `splitMatch` works fine.
  if Lean.Meta.Split.findSplit?.isCandidate (← getEnv) (e := e) (splitIte := false) then
    let new_goals ← Split.splitMatch goal e
    new_goals.forM (solveMono ur)
    return

  failK

private def replaceRecApps (recFnName : Name) (fixedPrefixSize : Nat) (F : Expr) (e : Expr) : Expr :=
  e.replace fun e =>
    if e.isAppOfArity recFnName fixedPrefixSize then
      some F
    else
      none

/-- Used in error messages -/
private def unReplaceRecApps (preDefs : Array PreDefinition) (argsPacker : ArgsPacker)
    (fixedArgs : Array Expr) : Unreplacer := fun f k => do
  unless f.isLambda do throwError "Expected lambda:{indentExpr f}"
  withoutModifyingEnv do
    preDefs.forM addAsAxiom
    let fns := preDefs.map (fun d => .const d.declName (d.levelParams.map mkLevelParam))
    let e ← lambdaBoundedTelescope f 1 fun f e =>
      let f := f[0]!
      return e.replace fun e => do
        guard e.isApp
        guard (e.appFn! == f)
        let (n, xs) ← argsPacker.unpack e.appArg!
        return mkAppN fns[n]! (fixedArgs ++ xs)
    k e

def derecursifyTailrec (fixedPrefixSize : Nat) (preDef : PreDefinition) (w : Expr)
    (unreplace : Array Expr → Unreplacer) :
    TermElabM PreDefinition := do
  forallBoundedTelescope preDef.type fixedPrefixSize fun prefixArgs type => do
    let unreplace := unreplace prefixArgs
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
      solveMono unreplace mono.mvarId!
    let value := .app value (← instantiateMVars mono)

    let value ← mkLambdaFVars prefixArgs value
    return { preDef with value }

def tailRecursion (preDefs : Array PreDefinition) : TermElabM Unit := do
  let witnesses ← preDefs.mapM fun preDef =>
    let msg := m!"failed to compile definition '{preDef.declName}' via tailrecursion"
    mkInhabitantFor msg #[] preDef.type
  trace[Elab.definition.tailrec] "Found nonempty witnesses: {witnesses}"

  let fixedPrefixSize ← getFixedPrefix preDefs
  trace[Elab.definition.tailrec] "fixed prefix size: {fixedPrefixSize}"
  let varNamess ← preDefs.mapM (varyingVarNames fixedPrefixSize ·)
  let argsPacker : ArgsPacker := { varNamess }

  let declNames := preDefs.map (·.declName)

  forallBoundedTelescope preDefs[0]!.type fixedPrefixSize fun fixedArgs _ => do
    let witnesses := witnesses.map (·.beta fixedArgs)
    let types ← preDefs.mapM (instantiateForall ·.type fixedArgs)
    let packedType ← argsPacker.uncurryType types
    let packedDomain := packedType.bindingDomain!

    let unaryWitness ← argsPacker.uncurry witnesses
    let inst1 ← withLocalDeclD `x packedDomain fun x => do
      mkLambdaFVars #[x] (← mkAppM ``Nonempty.intro #[.app unaryWitness x])

    let ur := unReplaceRecApps preDefs argsPacker
    -- let ur _ e k := k e

    -- Adjust the body of each function to take the other functions as a
    -- (packed) parameter
    let Fs ← preDefs.mapM fun preDef => do
      let body ← instantiateLambda preDef.value fixedArgs
      lambdaTelescope body fun xs body => do
        withLocalDeclD (← mkFreshUserName `f) packedType fun f => do
          let body' ← withoutModifyingEnv do
            -- WF.packCalls needs the constants in the env to typecheck things
            preDefs.forM (addAsAxiom ·)
            WF.packCalls fixedPrefixSize argsPacker declNames f body
          mkLambdaFVars (xs.push f) body'

    -- Construct and solve monotonicity goals for each function separately
    -- This way we preserve the users parameter names as much as possible
    -- and can (later) use the user-specified per-function tactic
    let hmonos ← preDefs.mapIdxM fun i preDef => do
      let type ← instantiateForall preDef.type fixedArgs
      let body ← instantiateLambda preDef.value fixedArgs
      lambdaTelescope body fun xs _ => do
        let type ← instantiateForall type xs
        let F ← instantiateLambda Fs[i]! xs
        let inst2 ← mkAppM ``Nonempty.intro #[mkAppN witnesses[i]! xs]
        let goal ← mkAppOptM ``Tailrec.mono #[packedDomain, none, type, inst1, inst2, F]
        let hmono ← mkFreshExprSyntheticOpaqueMVar goal
        mapError (f := (m!"Could not prove '{preDef.declName}' to be tailrecursive:{indentD ·}")) do
          solveMono (ur fixedArgs) hmono.mvarId!
        mkLambdaFVars xs (← instantiateMVars hmono)

    let FType ← withLocalDeclD `x packedDomain fun x => do
      mkForallFVars #[x] (← mkArrow packedType (← instantiateForall packedType #[x]))
    let F ← argsPacker.uncurryWithType FType Fs
    let value ← mkAppOptM ``Lean.Tailrec.tailrec_fix #[packedDomain, none, inst1, F]

    let monoGoal := (← inferType value).bindingDomain!
    let hmono ← argsPacker.uncurryWithType monoGoal hmonos
    let value := .app value hmono

    let packedType ← mkForallFVars fixedArgs packedType
    let value ← mkLambdaFVars fixedArgs value
    let preDefNonRec := { preDefs[0]! with
      declName := WF.mutualName argsPacker preDefs
      type := packedType
      value }
    addPreDefsFromUnary preDefs fixedPrefixSize argsPacker preDefNonRec (hasInduct := false)

end Lean.Elab

builtin_initialize Lean.registerTraceClass `Elab.definition.tailrec
