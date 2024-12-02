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

  let_expr Tailrec.monotone α inst_α β inst_β f := type |
    throwError "Unexpected goal:\n{goal}"

  unless f.isLambda do
    throwError "Unexpected goal:\n{goal}"

  let failK := do
    trace[Elab.definition.tailrec] "Failing at goal\n{goal}"
    ur f fun t => do
      if let some recApp := t.find? hasRecAppSyntax then
        let some syn := getRecAppSyntax? recApp | panic! "getRecAppSyntax? failed"
        withRef syn <|
          throwError "Recursive call `{syn}` is not a tail call.\nEnclosing tail-call position:{indentExpr t}"
      else
       throwError "Recursive call in non-tail position:{indentExpr t}"

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
    match_expr inst_α with
    | Tailrec.instOrderPi γ δ inst =>
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
    | _ =>
      failK

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

  -- Manually handle ite, dite, etc.. Not too hard, and more robust and predictable than
  -- using the split tactic.
  match_expr e with
  | ite _ cond decInst k₁ k₂ =>
    let us := type.getAppFn.constLevels!
    let k₁' := f.updateLambdaE! f.bindingDomain! k₁
    let k₂' := f.updateLambdaE! f.bindingDomain! k₂
    let p := mkAppN (.const ``Tailrec.monotone_ite us) #[α, inst_α, β, inst_β, cond, decInst, k₁', k₂']
    let new_goals ←
      mapError (f := (m!"Could not apply {p}:{indentD ·}}")) do
        goal.apply p
    new_goals.forM (solveMono ur)
    return
  | dite _ cond decInst k₁ k₂ =>
    let us := type.getAppFn.constLevels!
    let k₁' := f.updateLambdaE! f.bindingDomain! k₁
    let k₂' := f.updateLambdaE! f.bindingDomain! k₂
    let p := mkAppN (.const ``Tailrec.monotone_dite us) #[α, inst_α, β, inst_β, cond, decInst, k₁', k₂']
    let new_goals ←
      mapError (f := (m!"Could not apply {p}:{indentD ·}}")) do
        goal.apply p
    new_goals.forM (solveMono ur)
    return
  | letFun δ _ v k =>
    if k.isLambda then
      let us := type.getAppFn.constLevels! ++ e.getAppFn.constLevels!.take 1
      let k' := f.updateLambdaE! f.bindingDomain! k
      let p := mkAppN (.const ``Tailrec.monotone_letFun us) #[α, inst_α, β, inst_β, δ, v, k']
      let new_goals ←
        mapError (f := (m!"Could not apply {p}:{indentD ·}}")) do
          goal.apply p
      let [new_goal] := new_goals | throwError "Unexpected number of goals after applying {p}"
      -- Intro subgoal with the name found in the letFun expression
      let (_, new_goal) ← new_goal.intro k.bindingName!
      solveMono ur new_goal
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
    let instNonemptyRange ← withLocalDeclD `x packedDomain fun x => do
      mkLambdaFVars #[x] (← mkAppM ``Nonempty.intro #[.app unaryWitness x])
    let instOrderRange ← withLocalDeclD `x packedDomain fun x => do
      let instNonempty ← mkAppM ``Nonempty.intro #[.app unaryWitness x]
      let inst ← mkAppOptM ``Tailrec.FlatOrder.instOrder #[none, instNonempty]
      mkLambdaFVars #[x] inst
    let instOrderPackedType ←
      mkAppOptM ``Tailrec.instOrderPi #[packedDomain, none, instOrderRange]

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
    -- This way we preserve the user's parameter names as much as possible
    -- and can (later) use the user-specified per-function tactic
    let hmonos ← preDefs.mapIdxM fun i preDef => do
      let type ← instantiateForall preDef.type fixedArgs
      let body ← instantiateLambda preDef.value fixedArgs
      lambdaTelescope body fun xs _ => do
        let type ← instantiateForall type xs
        let F ← instantiateLambda Fs[i]! xs
        let instNonempty ← mkAppM ``Nonempty.intro #[mkAppN witnesses[i]! xs]
        let instOrder ← mkAppOptM ``Tailrec.FlatOrder.instOrder #[none, instNonempty]
        let goal ← mkAppOptM ``Tailrec.monotone
          #[packedType, instOrderPackedType, type, instOrder, F]
        let hmono ← mkFreshExprSyntheticOpaqueMVar goal
        mapError (f := (m!"Could not prove '{preDef.declName}' to be tailrecursive:{indentD ·}")) do
          solveMono (ur fixedArgs) hmono.mvarId!
        mkLambdaFVars xs (← instantiateMVars hmono)

    let FType ← withLocalDeclD `x packedDomain fun x => do
      mkForallFVars #[x] (← mkArrow packedType (← instantiateForall packedType #[x]))
    let F ← argsPacker.uncurryWithType FType Fs
    let packedValue ← mkAppOptM ``Lean.Tailrec.tailrec_fix
      #[packedDomain, none, instNonemptyRange, F]

    let monoGoal := (← inferType packedValue).bindingDomain!
    let hmono ← argsPacker.uncurryWithType monoGoal hmonos
    let packedValue := .app packedValue hmono
    let some packedValue ← delta? packedValue | panic! "Could not delta-reduce"

    let packedType ← mkForallFVars fixedArgs packedType
    let packedValue ← mkLambdaFVars fixedArgs packedValue
    let preDefNonRec := { preDefs[0]! with
      declName := WF.mutualName argsPacker preDefs
      type := packedType
      value := packedValue}
    addPreDefsFromUnary preDefs fixedPrefixSize argsPacker preDefNonRec (hasInduct := false)

end Lean.Elab

builtin_initialize Lean.registerTraceClass `Elab.definition.tailrec
