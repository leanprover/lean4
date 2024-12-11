/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
prelude
import Lean.Elab.PreDefinition.MkInhabitant
import Lean.Elab.PreDefinition.WF.PackMutual
import Lean.Elab.Tactic.Monotonicity
import Init.Internal.Order.Basic

namespace Lean.Elab

open Meta
open Monotonicity

open Lean.Order

private def replaceRecApps (recFnName : Name) (fixedPrefixSize : Nat) (F : Expr) (e : Expr) : Expr :=
  e.replace fun e =>
    if e.isAppOfArity recFnName fixedPrefixSize then
      some F
    else
      none

/--
For pretty error messages:
Takes `F : (fun f => e)`, where `f` is the packed function, and replaces `f` in `e` with the user-visible
constants, which are added to the environment temporarily.
-/
private def unReplaceRecApps {α} (preDefs : Array PreDefinition) (argsPacker : ArgsPacker)
    (fixedArgs : Array Expr) (F : Expr) (k : Expr → MetaM α) : MetaM α := do
  unless F.isLambda do throwError "Expected lambda:{indentExpr F}"
  withoutModifyingEnv do
    preDefs.forM addAsAxiom
    let fns := preDefs.map (fun d => .const d.declName (d.levelParams.map mkLevelParam))
    let e ← lambdaBoundedTelescope F 1 fun f e =>
      let f := f[0]!
      return e.replace fun e => do
        guard e.isApp
        guard (e.appFn! == f)
        let (n, xs) ← argsPacker.unpack e.appArg!
        return mkAppN fns[n]! (fixedArgs ++ xs)
    k e

def partialFixpoint (preDefs : Array PreDefinition) : TermElabM Unit := do
  -- For every function, an CCPO instance on its range
  -- ∀ x1 x2, CCPO (t1 x1 x2)
  let ccpoInsts ← preDefs.mapM fun preDef =>
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

  let fixedPrefixSize ← WF.getFixedPrefix preDefs
  trace[Elab.definition.partialFixpoint] "fixed prefix size: {fixedPrefixSize}"
  let varNamess ← preDefs.mapM (WF.varyingVarNames fixedPrefixSize ·)
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
         mkForallFVars #[x] (← mkAppM ``CCPO #[← instantiateForall packedType #[x]])
    let unaryCCPOInst ← argsPacker.uncurryWithType unaryCCPOInstType ccpoInsts
    -- ∀ (x : packedDomain): Order (t x). Derived from unaryCCPOInst to avoid diamond later on
    let unaryOrderInst ←
      withLocalDeclD `x packedDomain fun x => do
        mkLambdaFVars #[x] (← mkAppOptM ``CCPO.toOrder #[none, unaryCCPOInst.beta #[x]])
    -- CCPO (∀ (x : packedDomain): t x)
    let instCCPOPackedType ← mkAppOptM ``instCCPOPi #[packedDomain, packedRange, unaryCCPOInst]
    -- Order (∀ (x : packedDomain): t x)
    let instOrderPackedType ← mkAppOptM ``CCPO.toOrder #[packedType, instCCPOPackedType]

    -- Error reporting hook, preseting monotonicity errors in terms of recursive functions
    let failK {α} f (monoThms : Array Name) : MetaM α := do
      unReplaceRecApps preDefs argsPacker fixedArgs f fun t => do
        let extraMsg := if monoThms.isEmpty then m!"" else
          m!"Tried to apply {.andList (monoThms.toList.map (m!"'{.ofConstName ·}'"))}, but failed.\n\
             Possible cause: A missing `{.ofConstName ``MonoBind}` instance.\n\
             Use `set_option trace.Elab.definition.partialFixpoint true` to debug."
        if let some recApp := t.find? hasRecAppSyntax then
          let some syn := getRecAppSyntax? recApp | panic! "getRecAppSyntax? failed"
          withRef syn <|
            throwError "Recursive call `{syn}` is not a tail call.\nEnclosing tail-call position:{indentExpr t}\n{extraMsg}"
        else
          throwError "Recursive call in non-tail position:{indentExpr t}\n{extraMsg}"

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
        let instOrder ← mkAppOptM ``CCPO.toOrder #[none, ccpoInsts[i]!.beta xs]
        let goal ← mkAppOptM ``monotone
          #[packedType, instOrderPackedType, type, instOrder, F]
        let hmono ← mkFreshExprSyntheticOpaqueMVar goal
        mapError (f := (m!"Could not prove '{preDef.declName}' to be tailrecursive:{indentD ·}")) do
          solveMono failK hmono.mvarId!
        mkLambdaFVars xs (← instantiateMVars hmono)

    let FType ← withLocalDeclD `x packedDomain fun x => do
      mkForallFVars #[x] (← mkArrow packedType (← instantiateForall packedType #[x]))
    let F ← argsPacker.uncurryWithType FType Fs
    -- We still have to swap the arguments to F
    let F ←
      withLocalDeclD `f packedType fun f =>
        withLocalDeclD `x packedDomain fun x =>
          mkLambdaFVars #[f, x] (F.beta #[x, f])

    let hmono ← mkAppOptM ``monotone_of_monotone_apply
      #[packedDomain, packedRange, packedType, instOrderPackedType, unaryOrderInst, F]

    let monoGoal := (← inferType hmono).bindingDomain!
    trace[Elab.definition.partialFixpoint] "monoGoal: {monoGoal}"
    let hmono' ← argsPacker.uncurryWithType monoGoal hmonos
    let hmono := mkApp hmono hmono'

    let packedValue ← mkAppOptM ``fix #[packedType, instCCPOPackedType, F, hmono]
    trace[Elab.definition.partialFixpoint] "finalValue: {packedValue}"

    check packedValue

    let packedType ← mkForallFVars fixedArgs packedType
    let packedValue ← mkLambdaFVars fixedArgs packedValue
    let preDefNonRec := { preDefs[0]! with
      declName := WF.mutualName argsPacker preDefs
      type := packedType
      value := packedValue}
    WF.addPreDefsFromUnary preDefs fixedPrefixSize argsPacker preDefNonRec (hasInduct := false)

end Lean.Elab

builtin_initialize Lean.registerTraceClass `Elab.definition.partialFixpoint
