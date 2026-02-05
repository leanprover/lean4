/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Elab.Tactic.Basic
import Lean.Meta.Native
import Lean.Elab.Tactic.ElabTerm

public section

namespace Lean.Elab.Tactic
open Meta

/--
Make sure `expectedType` does not contain free and metavariables.
It applies zeta and zetaDelta-reduction to eliminate let-free-vars.
-/
private def preprocessPropToDecide (expectedType : Expr) : TermElabM Expr := do
  let mut expectedType ← instantiateMVars expectedType
  if expectedType.hasFVar then
    expectedType ← zetaReduce expectedType
  if expectedType.hasMVar then
    throwError "Expected type must not contain metavariables{indentExpr expectedType}"
  if expectedType.hasFVar then
    throwError m!"Expected type must not contain free variables{indentExpr expectedType}"
      ++ .hint' m!"Use the `+revert` option to automatically clean up and revert free variables"
  return expectedType

/--
Given the decidable instance `inst`, reduces it and returns a decidable instance expression
in whnf that can be regarded as the reason for the failure of `inst` to fully reduce.
-/
private partial def blameDecideReductionFailure (inst : Expr) : MetaM Expr := withIncRecDepth do
  let inst ← whnf inst
  -- If it's the Decidable recursor, then blame the major premise.
  if inst.isAppOfArity ``Decidable.rec 5 then
    return ← blameDecideReductionFailure inst.appArg!
  -- If it is a matcher, look for a discriminant that's a Decidable instance to blame.
  if let .const c _ := inst.getAppFn then
    if let some info ← getMatcherInfo? c then
      if inst.getAppNumArgs == info.arity then
        let args := inst.getAppArgs
        for i in *...info.numDiscrs do
          let inst' := args[info.numParams + 1 + i]!
          if (← Meta.isClass? (← inferType inst')) == ``Decidable then
            let inst'' ← whnf inst'
            if !(inst''.isAppOf ``isTrue || inst''.isAppOf ``isFalse) then
              return ← blameDecideReductionFailure inst''
  return inst

def elabNativeDecideCore (tacticName : Name) (expectedType : Expr) : TacticM Expr := do
  let d ← mkDecide expectedType
  match (← nativeEqTrue tacticName d (axiomDeclRange? := (← getRef))) with
  | .notTrue =>
    throwError m!"\
      Tactic `{tacticName}` evaluated that the proposition\
      {indentExpr expectedType}\n\
      is false"
  | .success prf =>
    -- get instance from `d`
    let s := d.appArg!
    return mkApp3 (mkConst ``of_decide_eq_true) expectedType s prf

def evalDecideCore (tacticName : Name) (cfg : Parser.Tactic.DecideConfig) : TacticM Unit := do
  if cfg.revert then
    -- In revert mode: clean up the local context and then revert everything that is left.
    liftMetaTactic1 fun g => do
      let g ← g.cleanup
      let (_, g) ← g.revert (clearAuxDeclsInsteadOfRevert := true) (← g.getDecl).lctx.getFVarIds
      return g
  closeMainGoalUsing tacticName fun expectedType _ => do
    if cfg.kernel && cfg.native then
      throwError "Tactic `{tacticName}` failed: Cannot simultaneously set both `+kernel` and `+native`"
    let expectedType ← preprocessPropToDecide expectedType
    if cfg.native then
      elabNativeDecideCore tacticName expectedType
    else if cfg.kernel then
      doKernel expectedType
    else
      doElab expectedType
where
  doElab (expectedType : Expr) : TacticM Expr := do
    let pf ← mkDecideProof expectedType
    -- Get instance from `pf`
    let s := pf.appFn!.appArg!
    let r ← withAtLeastTransparency .default <| whnf s
    if r.isAppOf ``isTrue then
      -- Success!
      -- While we have a proof from reduction, we do not embed it in the proof term,
      -- and instead we let the kernel recompute it during type checking from the following more
      -- efficient term. The kernel handles the unification `e =?= true` specially.
      return pf
    else
      -- Diagnose the failure, lazily so that there is no performance impact if `decide` isn't being used interactively.
      throwError MessageData.ofLazyM (es := #[expectedType]) do
        diagnose expectedType s r

  doKernel (expectedType : Expr) : TacticM Expr := do
    let pf ← mkDecideProof expectedType
    -- Get instance from `pf`
    let s := pf.appFn!.appArg!
    -- Reduce the decidable instance to (hopefully!) `isTrue` by passing `pf` to the kernel.
    -- The `mkAuxLemma` function caches the result in two ways:
    -- 1. First, the function makes use of a `type`-indexed cache per module.
    -- 2. Second, once the proof is added to the environment, the kernel doesn't need to check the proof again.
    let levelsInType := (collectLevelParams {} expectedType).params
    -- Level variables occurring in `expectedType`, in ambient order
    let lemmaLevels := (← Term.getLevelNames).reverse.filter levelsInType.contains
    try
      let lemmaName ← withOptions (Elab.async.set · false) do
        mkAuxLemma lemmaLevels expectedType pf
      return mkConst lemmaName (lemmaLevels.map .param)
    catch ex =>
      -- Diagnose the failure, lazily so that there is no performance impact if `decide` isn't being used interactively.
      throwError MessageData.ofLazyM (es := #[expectedType]) do
        let r ← withAtLeastTransparency .default <| whnf s
        if r.isAppOf ``isTrue then
          return m!"\
            Tactic `{tacticName}` failed. The elaborator is able to reduce the \
            `{.ofConstName ``Decidable}` instance, but the kernel fails with:\n\
            {indentD ex.toMessageData}"
        diagnose expectedType s r

  diagnose (expectedType s : Expr) (r : Expr) : MetaM MessageData := do
    if r.isAppOf ``isFalse then
      return m!"\
        Tactic `{tacticName}` proved that the proposition\
        {indentExpr expectedType}\n\
        is false"
    -- Re-reduce the instance and collect diagnostics, to get all unfolded Decidable instances
    let (reason, unfoldedInsts) ← withoutModifyingState <| withOptions (fun opt => diagnostics.set opt true) do
      modifyDiag (fun _ => {})
      let reason ← withAtLeastTransparency .default <| blameDecideReductionFailure s
      let unfolded := (← get).diag.unfoldCounter.foldl (init := #[]) fun cs n _ => cs.push n
      let unfoldedInsts ← unfolded |>.qsort Name.lt |>.filterMapM fun n => do
        let e ← mkConstWithLevelParams n
        if (← Meta.isClass? (← inferType e)) == ``Decidable then
          return m!"`{.ofConst e}`"
        else
          return none
      return (reason, unfoldedInsts)
    let stuckMsg :=
      if unfoldedInsts.isEmpty then
        m!"Reduction got stuck at the `{.ofConstName ``Decidable}` instance{indentExpr reason}"
      else
        let instances := if unfoldedInsts.size == 1 then "instance" else "instances"
        m!"After unfolding the {instances} {.andList unfoldedInsts.toList}, \
        reduction got stuck at the `{.ofConstName ``Decidable}` instance{indentExpr reason}"
    let hint :=
      if reason.isAppOf ``Eq.rec then
        .hint' m!"Reduction got stuck on `▸` ({.ofConstName ``Eq.rec}), \
          which suggests that one of the `{.ofConstName ``Decidable}` instances is defined using tactics such as `rw` or `simp`. \
          To avoid tactics, make use of functions such as \
          `{.ofConstName ``inferInstanceAs}` or `{.ofConstName ``decidable_of_decidable_of_iff}` \
          to alter a proposition."
      else if reason.isAppOf ``Classical.choice then
        .hint' m!"Reduction got stuck on `{.ofConstName ``Classical.choice}`, \
          which indicates that a `{.ofConstName ``Decidable}` instance \
          is defined using classical reasoning, proving an instance exists rather than giving a concrete construction. \
          The `{tacticName}` tactic works by evaluating a decision procedure via reduction, \
          and it cannot make progress with such instances. \
          This can occur due to the `open scoped Classical` command, which enables the instance \
          `{.ofConstName ``Classical.propDecidable}`."
      else
        MessageData.nil
    return m!"\
      Tactic `{tacticName}` failed for proposition\
      {indentExpr expectedType}\n\
      because its `{.ofConstName ``Decidable}` instance\
      {indentExpr s}\n\
      did not reduce to `{.ofConstName ``isTrue}` or `{.ofConstName ``isFalse}`.\n\n\
      {stuckMsg}{hint}"

declare_config_elab elabDecideConfig Parser.Tactic.DecideConfig

@[builtin_tactic Lean.Parser.Tactic.decide] def evalDecide : Tactic := fun stx => do
  let cfg ← elabDecideConfig stx[1]
  evalDecideCore `decide cfg

@[builtin_tactic Lean.Parser.Tactic.nativeDecide] def evalNativeDecide : Tactic := fun stx => do
  let cfg ← elabDecideConfig stx[1]
  let cfg := { cfg with native := true }
  evalDecideCore `native_decide cfg
