/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
prelude
import Lean.Elab.PreDefinition.MkInhabitant
import Lean.Elab.PreDefinition.Mutual
import Lean.Elab.PreDefinition.PartialFixpoint.Eqns
import Lean.Elab.Tactic.Monotonicity
import Init.Internal.Order.Basic
import Lean.Meta.PProdN

namespace Lean.Elab

open Meta
open Monotonicity

open Lean.Order

private def replaceRecApps (recFnNames : Array Name) (fixedParamPerms : FixedParamPerms) (f : Expr) (e : Expr) : MetaM Expr := do
  assert! recFnNames.size = fixedParamPerms.perms.size
  let t ← inferType f
  return e.replace fun e => do
    let fn := e.getAppFn
    guard fn.isConst
    let idx ← recFnNames.idxOf? fn.constName!
    let args := e.getAppArgs
    let varying := fixedParamPerms.perms[idx]!.pickVarying args
    return mkAppN (PProdN.proj recFnNames.size idx t f) varying

/--
For pretty error messages:
Takes `F : (fun f => e)`, where `f` is the packed function, and replaces `f` in `e` with the user-visible
constants, which are added to the environment temporarily.
-/
private def unReplaceRecApps {α} (preDefs : Array PreDefinition) (fixedParamPerms : FixedParamPerms) (fixedArgs : Array Expr)
    (F : Expr) (k : Expr → MetaM α) : MetaM α := do
  unless F.isLambda do throwError "Expected lambda:{indentExpr F}"
  withoutModifyingEnv do
    preDefs.forM addAsAxiom
    let fns ← preDefs.mapIdxM fun funIdx preDef => do
      let value ← fixedParamPerms.perms[funIdx]!.instantiateLambda preDef.value fixedArgs
      lambdaTelescope value fun xs _ =>
        let args := fixedParamPerms.perms[funIdx]!.buildArgs fixedArgs xs
        let call := mkAppN (.const preDef.declName (preDef.levelParams.map mkLevelParam)) args
        mkLambdaFVars (etaReduce := true) xs call
    let packedFn ← PProdN.mk 0 fns
    let e ← lambdaBoundedTelescope F 1 fun f e => do
      let f := f[0]!
      -- Replace f with calls to the constants
      let e := e.replace fun e => do
        if e == f then return packedFn else none
      -- And reduce projection and beta redexes
      -- (This is a bit blunt; we could try harder to only replace the projection and beta-redexes
      -- introduced above)
      let e ← PProdN.reduceProjs e
      let e ← Core.betaReduce e
      pure e
    k e

def mkInstCCPOPProd (inst₁ inst₂ : Expr) : MetaM Expr := do
  mkAppOptM ``instCCPOPProd #[none, none, inst₁, inst₂]

def mkMonoPProd (hmono₁ hmono₂ : Expr) : MetaM Expr := do
  -- mkAppM does not support the equivalent of (cfg := { synthAssignedInstances := false}),
  -- so this is a bit more pedestrian
  let_expr monotone _ inst _ inst₁ _ := (← inferType hmono₁)
    | throwError "mkMonoPProd: unexpected type of{indentExpr hmono₁}"
  let_expr monotone _ _ _ inst₂ _ := (← inferType hmono₂)
    | throwError "mkMonoPProd: unexpected type of{indentExpr hmono₂}"
  mkAppOptM ``PProd.monotone_mk #[none, none, none, inst₁, inst₂, inst, none, none, hmono₁, hmono₂]

def partialFixpoint (preDefs : Array PreDefinition) : TermElabM Unit := do
  -- We expect all functions in the clique to have `partial_fixpoint` syntax
  let hints := preDefs.filterMap (·.termination.partialFixpoint?)
  assert! preDefs.size = hints.size
  -- For every function of type `∀ x y, r x y`, an CCPO instance
  -- ∀ x y, CCPO (r x y), but crucially constructed using `instCCPOPi`
  let ccpoInsts ← preDefs.mapIdxM fun i preDef => withRef hints[i]!.ref do
    lambdaTelescope preDef.value fun xs _body => do
      let type ← instantiateForall preDef.type xs
      let inst ←
        try
          synthInstance (← mkAppM ``CCPO #[type])
        catch _ =>
          trace[Elab.definition.partialFixpoint] "No CCPO instance found for {preDef.declName}, trying inhabitation"
          let msg := m!"failed to compile definition '{preDef.declName}' using `partial_fixpoint`"
          let w ← mkInhabitantFor msg #[] preDef.type
          let instNonempty ← mkAppM ``Nonempty.intro #[mkAppN w xs]
          let classicalWitness ← mkAppOptM ``Classical.ofNonempty #[none, instNonempty]
          mkAppOptM ``FlatOrder.instCCPO #[none, classicalWitness]
      mkLambdaFVars xs inst

  let declNames := preDefs.map (·.declName)
  let fixedParamPerms ← getFixedParamPerms preDefs
  fixedParamPerms.perms[0]!.forallTelescope preDefs[0]!.type fun fixedArgs => do
    -- ∀ x y, CCPO (rᵢ x y)
    let ccpoInsts ← ccpoInsts.mapIdxM (fixedParamPerms.perms[·]!.instantiateLambda · fixedArgs)
    let types ← preDefs.mapIdxM (fixedParamPerms.perms[·]!.instantiateForall ·.type fixedArgs)

    -- (∀ x y, r₁ x y) ×' (∀ x y, r₂ x y)
    let packedType ← PProdN.pack 0 types

    -- CCPO (∀ x y, rᵢ x y)
    let ccpoInsts' ← ccpoInsts.mapM fun inst =>
      lambdaTelescope inst fun xs inst => do
        let mut inst := inst
        for x in xs.reverse do
          inst ← mkAppOptM ``instCCPOPi #[(← inferType x), none, (← mkLambdaFVars #[x] inst)]
        pure inst
    -- CCPO ((∀ x y, r₁ x y) ×' (∀ x y, r₂ x y))
    let packedCCPOInst ← PProdN.genMk mkInstCCPOPProd ccpoInsts'
    -- Order ((∀ x y, r₁ x y) ×' (∀ x y, r₂ x y))
    let packedPartialOrderInst ← mkAppOptM ``CCPO.toPartialOrder #[none, packedCCPOInst]

    -- Error reporting hook, presenting monotonicity errors in terms of recursive functions
    let failK {α} f (monoThms : Array Name) : MetaM α := do
      unReplaceRecApps preDefs fixedParamPerms fixedArgs f fun t => do
        let extraMsg := if monoThms.isEmpty then m!"" else
          m!"Tried to apply {.andList (monoThms.toList.map (m!"'{.ofConstName ·}'"))}, but failed.\n\
             Possible cause: A missing `{.ofConstName ``MonoBind}` instance.\n\
             Use `set_option trace.Elab.Tactic.monotonicity true` to debug."
        if let some recApp := t.find? hasRecAppSyntax then
          let some syn := getRecAppSyntax? recApp | panic! "getRecAppSyntax? failed"
          withRef syn <|
            throwError "Cannot eliminate recursive call `{syn}` enclosed in{indentExpr t}\n{extraMsg}"
        else
          throwError "Cannot eliminate recursive call in{indentExpr t}\n{extraMsg}"

    -- Adjust the body of each function to take the other functions as a
    -- (packed) parameter
    let Fs ← preDefs.mapIdxM fun funIdx preDef => do
      let body ← fixedParamPerms.perms[funIdx]!.instantiateLambda preDef.value fixedArgs
      withLocalDeclD (← mkFreshUserName `f) packedType fun f => do
        let body' ← withoutModifyingEnv do
          -- replaceRecApps needs the constants in the env to typecheck things
          preDefs.forM (addAsAxiom ·)
          replaceRecApps declNames fixedParamPerms f body
        mkLambdaFVars #[f] body'

    -- Construct and solve monotonicity goals for each function separately
    -- This way we preserve the user's parameter names as much as possible
    -- and can (later) use the user-specified per-function tactic
    let hmonos ← preDefs.mapIdxM fun i preDef => do
      let type := types[i]!
      let F := Fs[i]!
      let inst ← mkAppOptM ``CCPO.toPartialOrder #[type, ccpoInsts'[i]!]
      let goal ← mkAppOptM ``monotone #[packedType, packedPartialOrderInst, type, inst, F]
      if let some term := hints[i]!.term? then
        let hmono ← Term.withSynthesize <| Term.elabTermEnsuringType term goal
        let hmono ← instantiateMVars hmono
        let mvars ← getMVars hmono
        if mvars.isEmpty then
          pure hmono
        else
          discard <| Term.logUnassignedUsingErrorInfos mvars
          mkSorry goal (synthetic := true)
      else
        let hmono ← mkFreshExprSyntheticOpaqueMVar goal
        mapError (f := (m!"Could not prove '{preDef.declName}' to be monotone in its recursive calls:{indentD ·}")) do
          solveMono failK hmono.mvarId!
        trace[Elab.definition.partialFixpoint] "monotonicity proof for {preDef.declName}: {hmono}"
        instantiateMVars hmono
    let hmono ← PProdN.genMk mkMonoPProd hmonos

    let packedValue ← mkAppOptM ``fix #[packedType, packedCCPOInst, none, hmono]
    trace[Elab.definition.partialFixpoint] "packedValue: {packedValue}"

    let declName :=
      if preDefs.size = 1 && fixedParamPerms.fixedArePrefix then
        preDefs[0]!.declName
      else
        preDefs[0]!.declName ++ `mutual
    let packedType' ← mkForallFVars fixedArgs packedType
    let packedValue' ← mkLambdaFVars fixedArgs packedValue
    let preDefNonRec := { preDefs[0]! with
      declName := declName
      type := packedType'
      value := packedValue'}

    let preDefsNonrec ← preDefs.mapIdxM fun fidx preDef => do
      forallBoundedTelescope preDef.type fixedParamPerms.perms[fidx]!.size fun params _ => do
        let fixed := fixedParamPerms.perms[fidx]!.pickFixed params
        let varying := fixedParamPerms.perms[fidx]!.pickVarying params
        let us := preDefNonRec.levelParams.map mkLevelParam
        let value := mkConst preDefNonRec.declName us
        let value := mkAppN value fixed
        let value := PProdN.proj preDefs.size fidx packedType value
        let value := mkAppN value varying
        let value ← mkLambdaFVars (etaReduce := true) params value
        pure { preDef with value }

    Mutual.addPreDefsFromUnary preDefs preDefsNonrec preDefNonRec
    let preDefs ← Mutual.cleanPreDefs preDefs
    PartialFixpoint.registerEqnsInfo preDefs preDefNonRec.declName fixedParamPerms
    Mutual.addPreDefAttributes preDefs

end Lean.Elab

builtin_initialize Lean.registerTraceClass `Elab.definition.partialFixpoint
