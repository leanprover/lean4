/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Elab.PreDefinition.MkInhabitant
import Lean.Elab.PreDefinition.WF.PackMutual

namespace Lean.Elab
open WF
open Meta

/--
For pretty error messages:
Takes `fun f => e`, where `f` is the packed function, and replaces `f` in `e` with the user-visible
constants, which are added to the environment temporarily.
-/
abbrev Unreplacer := Expr → (Expr → MetaM Unit) → MetaM Unit

partial def headBetaUnderLambda (f : Expr) : Expr := Id.run do
  let mut f := f.headBeta
  if f.isLambda then
    while f.bindingBody!.isHeadBetaTarget do
      f := f.updateLambda! f.bindingInfo! f.bindingDomain! f.bindingBody!.headBeta
  return f

partial def solveMono (ur : Unreplacer) (goal : MVarId) : MetaM Unit := goal.withContext do
  trace[Elab.definition.tailrec] "solveMono at\n{goal}"
  let type ← goal.getType
  if type.isForall then
    let (_, goal) ← goal.intro1P
    solveMono ur goal
    return

  match_expr type with
  | Tailrec.forall_arg _α _β _γ _P f =>
    let f ← instantiateMVars f
    let f := headBetaUnderLambda f
    if f.isLambda && f.bindingBody!.isLambda then
      let name := f.bindingBody!.bindingName!
      let (_, new_goal) ← goal.intro name
      solveMono ur new_goal
    else
      let (_, new_goal) ← goal.intro1
      solveMono ur new_goal

  | Tailrec.monotone α inst_α β inst_β f =>
    -- Ensure f is headed not a redex and headed by at least one lambda, and clean some
    -- redexes left by some of the lemmas we tend to apply
    let f ← instantiateMVars f
    let f := f.headBeta
    let f ← if f.isLambda then pure f else etaExpand f
    let f := headBetaUnderLambda f

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
    | ite _ _ _ _ _ =>
      let new_goals ←
        mapError (f := (m!"Could not apply {``Tailrec.monotone_ite}:{indentD ·}")) do
          goal.applyConst ``Tailrec.monotone_ite (cfg := { synthAssignedInstances := false})
      new_goals.forM (solveMono ur)
      return
    | dite _ _ _ _ _ =>
      let new_goals ←
        mapError (f := (m!"Could not apply {``Tailrec.monotone_dite}:{indentD ·}")) do
          goal.applyConst ``Tailrec.monotone_dite (cfg := { synthAssignedInstances := false})
      new_goals.forM (solveMono ur)
      return
    | letFun _ _ _ _ =>
      let new_goals ←
        mapError (f := (m!"Could not apply {``Tailrec.monotone_letFun}:{indentD ·}")) do
          goal.applyConst ``Tailrec.monotone_letFun (cfg := { synthAssignedInstances := false})
      new_goals.forM (solveMono ur)
      return
    | Bind.bind _ _ _ _ _ _ =>
      let new_goals ←
        mapError (f := (m!"Could not apply {``Tailrec.monotone_bind}:{indentD ·}")) do
          goal.applyConst ``Tailrec.monotone_bind (cfg := { synthAssignedInstances := false})
      new_goals.forM (solveMono ur)
      return
    | List.mapM _ _ _ _ _ _ =>
      let new_goals ←
        mapError (f := (m!"Could not apply {``Tailrec.monotone_mapM }:{indentD ·}}")) do
          goal.applyConst ``Tailrec.monotone_mapM (cfg := { synthAssignedInstances := false})
      new_goals.forM (solveMono ur)
      return
    | Array.mapFinIdxM _ _ _ _ _ _ =>
      let new_goals ←
        mapError (f := (m!"Could not apply {``Tailrec.monotone_mapFinIdxM}:{indentD ·}}")) do
          goal.applyConst ``Tailrec.monotone_mapFinIdxM (cfg := { synthAssignedInstances := false})
      new_goals.forM (solveMono ur)
      return
    | _ => pure

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
        new_goals.forM (solveMono ur)
        return

    failK
  | _ =>
    throwError "Unexpected goal:{goal}"

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
  -- For every function, an CCPO instance on its range
  -- ∀ x1 x2, CCPO (t1 x1 x2)
  let ccpoInsts ← preDefs.mapM fun preDef =>
    lambdaTelescope preDef.value fun xs _body => do
      let type ← instantiateForall preDef.type xs
      let inst ←
        try
          synthInstance (← mkAppM ``Tailrec.CCPO #[type])
        catch _ =>
          trace[Elab.definition.tailrec] "No CCPO instance found for {preDef.declName}, trying inhabitation"
          let msg := m!"failed to compile definition '{preDef.declName}' via tailrecursion"
          let w ← mkInhabitantFor msg #[] preDef.type
          let instNonempty ← mkAppM ``Nonempty.intro #[mkAppN w xs]
          let classicalWitness ← mkAppOptM ``Classical.ofNonempty #[none, instNonempty]
          mkAppOptM ``Tailrec.FlatOrder.instCCPO #[none, classicalWitness]
      mkLambdaFVars xs inst

  let fixedPrefixSize ← getFixedPrefix preDefs
  trace[Elab.definition.tailrec] "fixed prefix size: {fixedPrefixSize}"
  let varNamess ← preDefs.mapM (varyingVarNames fixedPrefixSize ·)
  let argsPacker : ArgsPacker := { varNamess }

  let declNames := preDefs.map (·.declName)

  forallBoundedTelescope preDefs[0]!.type fixedPrefixSize fun fixedArgs _ => do
    let ccpoInsts := ccpoInsts.map (·.beta fixedArgs)
    let types ← preDefs.mapM (instantiateForall ·.type fixedArgs)
    let packedType ← argsPacker.uncurryType types
    let packedDomain := packedType.bindingDomain!
    let packedRange ← withLocalDeclD `x packedDomain fun x => do
      mkLambdaFVars #[x] (← instantiateForall packedType #[x])

    -- ∀ (x : packedDomain): CCPO (t x)
    let unaryCCPOInstType ←
      withLocalDeclD `x packedDomain fun x => do
         mkForallFVars #[x] (← mkAppM ``Tailrec.CCPO #[← instantiateForall packedType #[x]])
    let unaryCCPOInst ← argsPacker.uncurryWithType unaryCCPOInstType ccpoInsts
    -- ∀ (x : packedDomain): Order (t x). Derived from unaryCCPOInst to avoid diamond later on
    let unaryOrderInst ←
      withLocalDeclD `x packedDomain fun x => do
        mkLambdaFVars #[x] (← mkAppOptM ``Tailrec.CCPO.toOrder #[none, unaryCCPOInst.beta #[x]])
    -- CCPO (∀ (x : packedDomain): t x)
    let instCCPOPackedType ← mkAppOptM ``Tailrec.instCCPOPi #[packedDomain, packedRange, unaryCCPOInst]
    -- Order (∀ (x : packedDomain): t x)
    let instOrderPackedType ← mkAppOptM ``Tailrec.CCPO.toOrder #[packedType, instCCPOPackedType]

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
        let instOrder ← mkAppOptM ``Tailrec.CCPO.toOrder #[none, ccpoInsts[i]!.beta xs]
        let goal ← mkAppOptM ``Tailrec.monotone
          #[packedType, instOrderPackedType, type, instOrder, F]
        let hmono ← mkFreshExprSyntheticOpaqueMVar goal
        mapError (f := (m!"Could not prove '{preDef.declName}' to be tailrecursive:{indentD ·}")) do
          solveMono (ur fixedArgs) hmono.mvarId!
        mkLambdaFVars xs (← instantiateMVars hmono)

    let FType ← withLocalDeclD `x packedDomain fun x => do
      mkForallFVars #[x] (← mkArrow packedType (← instantiateForall packedType #[x]))
    let F ← argsPacker.uncurryWithType FType Fs
    -- We still have to swap the arguments to F
    let F ←
      withLocalDeclD `f packedType fun f =>
        withLocalDeclD `x packedDomain fun x =>
          mkLambdaFVars #[f, x] (F.beta #[x, f])

    let hmono ← mkAppOptM ``Tailrec.monotone_of_monotone_apply
      #[packedDomain, packedRange, packedType, instOrderPackedType, unaryOrderInst, F]

    let monoGoal := (← inferType hmono).bindingDomain!
    trace[Elab.definition.tailrec] "monoGoal: {monoGoal}"
    let hmono' ← argsPacker.uncurryWithType monoGoal hmonos
    let hmono := mkApp hmono hmono'

    let packedValue ← mkAppOptM ``Lean.Tailrec.fix #[packedType, instCCPOPackedType, F, hmono]
    trace[Elab.definition.tailrec] "finalValue: {packedValue}"

    check packedValue

    let packedType ← mkForallFVars fixedArgs packedType
    let packedValue ← mkLambdaFVars fixedArgs packedValue
    let preDefNonRec := { preDefs[0]! with
      declName := WF.mutualName argsPacker preDefs
      type := packedType
      value := packedValue}
    addPreDefsFromUnary preDefs fixedPrefixSize argsPacker preDefNonRec (hasInduct := false)

end Lean.Elab

builtin_initialize Lean.registerTraceClass `Elab.definition.tailrec
