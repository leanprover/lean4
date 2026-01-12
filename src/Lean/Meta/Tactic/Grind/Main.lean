/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Types
public import Lean.Meta.Tactic.Grind.Util
public import Lean.Meta.Closure
import Lean.PrettyPrinter
import Lean.Meta.Tactic.ExposeNames
import Lean.Meta.Tactic.Simp.Diagnostics
import Lean.Meta.Tactic.Simp.Rewrite
import Lean.Meta.Tactic.Grind.Split
import Lean.Meta.Tactic.Grind.RevertAll
import Lean.Meta.Tactic.Grind.PropagatorAttr
import Lean.Meta.Tactic.Grind.Proj
import Lean.Meta.Tactic.Grind.ForallProp
import Lean.Meta.Tactic.Grind.CtorIdx
import Lean.Meta.Tactic.Grind.Inv
import Lean.Meta.Tactic.Grind.Intro
import Lean.Meta.Tactic.Grind.EMatch
import Lean.Meta.Tactic.Grind.Solve
import Lean.Meta.Tactic.Grind.Internalize
import Lean.Meta.Tactic.Grind.SimpUtil
import Lean.Meta.Tactic.Grind.LawfulEqCmp
import Lean.Meta.Tactic.Grind.ReflCmp
import Lean.Meta.Tactic.Grind.PP
import Lean.Meta.Tactic.Grind.Simp
import Lean.Meta.Tactic.Grind.Core
public section
namespace Lean.Meta.Grind

/--
Returns the `ExtensionState` for the default `grind` attribute.
-/
def getDefaultExtensionState : MetaM ExtensionState :=
  return grindExt.getState (← getEnv)

def getOnlyExtensionState : MetaM ExtensionState := do
  let s := grindExt.getState (← getEnv)
  let casesTypes := s.casesTypes
  let funCC := s.funCC
  let extThms := s.extThms
  return {
    casesTypes, funCC, extThms
  }

structure Params where
  config      : Grind.Config
  extensions  : ExtensionStateArray := #[]
  extra       : PArray EMatchTheorem := {}
  extraInj    : PArray InjectiveTheorem := {}
  extraFacts  : PArray Expr := {}
  symPrios    : SymbolPriorities := {}
  norm        : Simp.Context
  normProcs   : Array Simprocs
  anchorRefs? : Option (Array AnchorRef) := none
  -- TODO: inductives to split

def mkParams (config : Grind.Config) (extensions : ExtensionStateArray) : MetaM Params := do
  let norm ← Grind.getSimpContext config
  let normProcs ← Grind.getSimprocs
  let symPrios ← getGlobalSymbolPriorities
  return { config, norm, normProcs, symPrios, extensions }

def mkDefaultParams (config : Grind.Config) : MetaM Params := do
  mkParams config #[← getDefaultExtensionState]

def mkOnlyParams (config : Grind.Config) : MetaM Params := do
  mkParams config #[← getOnlyExtensionState]

def mkMethods (evalTactic? : Option EvalTactic := none) : CoreM Methods := do
  let builtinPropagators ← builtinPropagatorsRef.get
  let evalTactic : EvalTactic := evalTactic?.getD EvalTactic.skip
  return {
    evalTactic
    propagateUp := fun e => do
      propagateForallPropUp e
      propagateReflCmp e
      let .const declName _ := e.getAppFn | return ()
      propagateProjEq e
      propagateCtorIdxUp e
      if let some props := builtinPropagators.up[declName]? then
       props.forM fun prop => prop e
    propagateDown := fun e => do
      propagateForallPropDown e
      propagateLawfulEqCmp e
      let .const declName _ := e.getAppFn | return ()
      if let some props := builtinPropagators.down[declName]? then
       props.forM fun prop => prop e
  }

-- A `simp` discharger that does not use assumptions.
-- We use it to make sure we don't have to reset the `simp` cache used in `grind`.
private def discharge? (e : Expr) : SimpM (Option Expr) := do
  let e := e.cleanupAnnotations
  let r ← Simp.simp e
  if let some p ← Simp.dischargeRfl r.expr then
    return some (mkApp4 (mkConst ``Eq.mpr [levelZero]) e r.expr (← r.getProof) p)
  else if r.expr.isTrue then
    return some (← mkOfEqTrue (← r.getProof))
  else
    return none

open Sym

def GrindM.run (x : GrindM α) (params : Params) (evalTactic? : Option EvalTactic := none) : MetaM α := Sym.SymM.run do
  let falseExpr  ← share <| mkConst ``False
  let trueExpr   ← share <| mkConst ``True
  let bfalseExpr ← share <| mkConst ``Bool.false
  let btrueExpr  ← share <| mkConst ``Bool.true
  let natZExpr   ← share <| mkNatLit 0
  let ordEqExpr  ← share <| mkConst ``Ordering.eq
  let intExpr    ← share <| Int.mkType
  /- **Note**: Consider using `Sym.simp` in the future. -/
  let simprocs  := params.normProcs
  let simpMethods := Simp.mkMethods simprocs discharge? (wellBehavedDischarge := true)
  let simp   := params.norm
  let config := params.config
  let symPrios := params.symPrios
  let extensions := params.extensions
  let anchorRefs? := params.anchorRefs?
  let debug := grind.debug.get (← getOptions)
  x (← mkMethods evalTactic?).toMethodsRef
    { config, anchorRefs?, simpMethods, simp, extensions, symPrios
      trueExpr, falseExpr, natZExpr, btrueExpr, bfalseExpr, ordEqExpr, intExpr
      debug }
    |>.run' {}

private def mkCleanState (mvarId : MVarId) : GrindM Clean.State := mvarId.withContext do
  let config ← getConfig
  unless config.clean do return {}
  let mut used : PHashSet Name := {}
  for localDecl in (← getLCtx) do
    used := used.insert localDecl.userName
  return { used }

/--
Asserts extra facts provided as `grind` parameters.
-/
def assertExtra (params : Params) : GoalM Unit := do
  for proof in params.extraFacts do
    let prop ← inferType proof
    addNewRawFact proof prop 0 .input
  for thm in params.extra do
    activateTheorem thm 0
  for thm in params.extraInj do
    activateInjectiveTheorem thm 0

private def initENodeCore (e : Expr) (interpreted ctor : Bool) : GoalM Unit := do
  if let .const declName _ := e then
    updateIndicesFound (.const declName)
  mkENodeCore e interpreted ctor (generation := 0) (funCC := false)

/-- Returns a new goal for the given metavariable. -/
public def mkGoal (mvarId : MVarId) : GrindM Goal := do
  let config ← getConfig
  let mvarId ← if config.clean then mvarId.exposeNames else pure mvarId
  let trueExpr ← getTrueExpr
  let falseExpr ← getFalseExpr
  let btrueExpr ← getBoolTrueExpr
  let bfalseExpr ← getBoolFalseExpr
  let natZeroExpr ← getNatZeroExpr
  let ordEqExpr ← getOrderingEqExpr
  let extensions ← getExtensions
  let thmEMatch := extensions.map fun ext => ext.ematch
  let thmInj := extensions.map fun ext => ext.inj
  let clean ← mkCleanState mvarId
  let sstates ← Solvers.mkInitialStates
  GoalM.run' { mvarId, ematch.thmMap := thmEMatch, inj.thms := thmInj, clean, sstates } do
    initENodeCore falseExpr (interpreted := true) (ctor := false)
    initENodeCore trueExpr (interpreted := true) (ctor := false)
    initENodeCore btrueExpr (interpreted := false) (ctor := true)
    initENodeCore bfalseExpr (interpreted := false) (ctor := true)
    initENodeCore natZeroExpr (interpreted := true) (ctor := false)
    initENodeCore ordEqExpr (interpreted := false) (ctor := true)

structure Result where
  failure?   : Option Goal
  issues     : List MessageData
  config     : Grind.Config
  counters   : Counters
  simp       : Simp.Stats
  splitDiags : PArray SplitDiagInfo

private def countersToMessageData (header : String) (cls : Name) (data : Array (Name × Nat)) : MetaM MessageData := do
  let data := data.qsort fun (d₁, c₁) (d₂, c₂) => if c₁ == c₂ then Name.lt d₁ d₂ else c₁ > c₂
  let data ← data.mapM fun (declName, counter) =>
    return .trace { cls } m!"{.ofConst (← mkConstWithLevelParams declName)} ↦ {counter}" #[]
  return .trace { cls } header data

private def splitDiagInfoToMessageData (ss : Array SplitDiagInfo) : MetaM MessageData := do
  let env  ← getEnv
  let mctx ← getMCtx
  let opts ← getOptions
  let cls := `split
  let data ← ss.mapM fun { c, lctx, numCases, gen, splitSource } => do
    let header := m!"{c}"
    return MessageData.withContext { env, mctx, lctx, opts } <| .trace { cls } header #[
      .trace { cls } m!"source: {splitSource.toMessageData}" #[],
      .trace { cls } m!"generation: {gen}" #[],
      .trace { cls } m!"# cases: {numCases}" #[]
    ]
  return .trace { cls } "Case splits" data

-- Diagnostics information for the whole search
private def mkGlobalDiag (cs : Counters) (simp : Simp.Stats) (ss : PArray SplitDiagInfo) : MetaM (Option MessageData) := do
  let thms := cs.thm.toList.toArray.filterMap fun (origin, c) =>
    match origin with
    | .decl declName => some (declName, c)
    | _ => none
  -- We do not report `cases` applications on builtin types
  let cases := cs.case.toList.toArray.filter fun (declName, _) => !isBuiltinEagerCases declName
  let mut msgs := #[]
  unless thms.isEmpty do
    msgs := msgs.push <| (← countersToMessageData "E-Matching instances" `thm thms)
  let ss := ss.toArray.filter fun { numCases, .. } => numCases > 1
  unless ss.isEmpty do
    msgs := msgs.push <| (← splitDiagInfoToMessageData ss)
  unless cases.isEmpty do
    msgs := msgs.push <| (← countersToMessageData "Cases instances" `cases cases)
  unless cs.apps.isEmpty do
    msgs := msgs.push <| (← countersToMessageData "Applications" `app cs.apps.toList.toArray)
  let simpMsgs ← Simp.mkDiagMessages simp.diag
  unless simpMsgs.isEmpty do
    msgs := msgs.push <| .trace { cls := `grind} "Simplifier" simpMsgs
  if msgs.isEmpty then
    return none
  else
    return some <| .trace { cls := `grind } "Diagnostics" msgs

def Result.hasFailed (r : Result) : Bool :=
  r.failure?.isSome

def Result.toMessageData (result : Result) : MetaM MessageData := do
  let mut msgs ← result.failure?.toList.mapM (goalToMessageData · result.config)
  if result.config.verbose then
    let mut issues := result.issues
    -- We did not find the following very useful in practice.
    /-
    unless result.skipped.isEmpty do
      let m := m!"#{result.skipped.length} other goal(s) were not fully processed due to previous failures, threshold: `(failures := {result.config.failures})`"
      issues := .trace { cls := `issue } m #[] :: issues
    -/
    unless issues.isEmpty do
      msgs := msgs ++ [.trace { cls := `grind } "Issues" issues.reverse.toArray]
    if let some msg ← mkGlobalDiag result.counters result.simp result.splitDiags then
      msgs := msgs ++ [msg]
  return MessageData.joinSep msgs m!"\n"

/--
When `Config.revert := false`, we preprocess the hypotheses, and add them to the `grind` state.
It starts at `goal.nextDeclIdx`. If `num?` is `some num`, then at most `num` local declarations are processed.
Otherwise, all remaining local declarations are processed.

Remark: this function assumes the local context does not contains holes with `none` in `decls`.
-/
def processHypotheses (goal : Goal) (num? : Option Nat := none) : GrindM Goal := GoalM.run' goal do
  discard <| go.run
where
  go : ExceptT Unit GoalM Unit := do
    let mvarDecl ← goal.mvarId.getDecl
    mvarDecl.lctx.forM (start := goal.nextDeclIdx) fun localDecl => do
      if (← isInconsistent) then
        setNextDeclToEnd
        throwThe Unit () -- interrupt
      if let some num := num? then
        if localDecl.index >= goal.nextDeclIdx + num then
          modify fun goal => { goal with nextDeclIdx := localDecl.index }
          throwThe Unit () -- interrupt
      unless localDecl.isImplementationDetail do
        let type := localDecl.type
        if (← isProp type) then
          let r ← preprocessHypothesis type
          match r.proof? with
          | none => add r.expr localDecl.toExpr
          | some h => add r.expr <| mkApp4 (mkConst ``Eq.mp [0]) type r.expr h localDecl.toExpr
        else
          internalizeLocalDecl localDecl
    setNextDeclToEnd -- Processed all local decls

private def initCore (mvarId : MVarId) : GrindM Goal := do
  let config ← getConfig
  let mvarId ← if config.clean || !config.revert then pure mvarId else mvarId.markAccessible
  let mvarId ← if config.revert then mvarId.revertAll else pure mvarId
  let mvarId ← mvarId.unfoldReducible
  let mvarId ← mvarId.betaReduce
  appendTagSuffix mvarId `grind
  let goal ← mkGoal mvarId
  if config.revert then
    return goal
  else
    processHypotheses goal

def mkResult (params : Params) (failure? : Option Goal) : GrindM Result := do
  let issues     := (← get).issues
  let counters   := (← get).counters
  let splitDiags := (← get).splitDiags
  let simp       := { (← get).simp with }
  if failure?.isNone then
    -- If there are no failures and diagnostics are enabled, we still report the performance counters.
    if (← isDiagnosticsEnabled) then
      if let some msg ← mkGlobalDiag counters simp splitDiags then
        logInfo msg
  return { failure?, issues, config := params.config, counters, simp, splitDiags }

def GrindM.runAtGoal (mvarId : MVarId) (params : Params) (k : Goal → GrindM α) (evalTactic? : Option EvalTactic := none) : MetaM α := do
  let go : GrindM α := withGTransparency do
    let goal ← initCore mvarId
    let goal ← GoalM.run' goal <| assertExtra params
    k goal
  go.run params (evalTactic? := evalTactic?)

def main (mvarId : MVarId) (params : Params) : MetaM Result := do profileitM Exception "grind" (← getOptions) do
  GrindM.runAtGoal mvarId params fun goal => do
    let failure? ← solve goal
    mkResult params failure?

/--
A helper combinator for executing a `grind`-based terminal tactic.
Given an input goal `mvarId`, it first abstracts meta-variables, cleans up local hypotheses
corresponding to internal details, creates an auxiliary meta-variable `mvarId'`, and executes `k mvarId'`.
The execution is performed in a new meta-variable context depth to ensure that universe meta-variables
cannot be accidentally assigned by `grind`. If `k` fails, it admits the input goal.

See issue #11806 for a motivating example.
-/
def withProtectedMCtx [Monad m] [MonadControlT MetaM m] [MonadLiftT MetaM m]
    [MonadExcept Exception m] [MonadRuntimeException m]
    (config : Grind.Config) (mvarId : MVarId) (k : MVarId → m α) : m α := do
  /-
  **Note**: `instantiateGoalMVars` here also instantiates mvars occurring in hypotheses.
  This is particularly important when using `grind -revert`.
  -/
  let mut mvarId ← mvarId.instantiateGoalMVars
  /-
  **TODO**: It would be nice to remove the following step, but
  some tests break with unknown metavariable error when this
  step is removed. The main issue is the `withNewMCtxDepth` step at
  `main`.
  -/
  mvarId ← mvarId.abstractMVars
  if config.revert then
    /-
    **Note**: We now skip implementation details at `addHypotheses`
    -/
    mvarId ← mvarId.clearImplDetails
  tryCatchRuntimeEx (main mvarId) fun ex => do
    mvarId.admit
    throw ex
where
  main (mvarId : MVarId) : m α := mvarId.withContext do
    let type ← mvarId.getType
    let (a, val) ← withNewMCtxDepth do
      let mvar' ← mkFreshExprSyntheticOpaqueMVar type
      let a ← k mvar'.mvarId!
      let val ← instantiateMVarsProfiling mvar'
      return (a, val)
    let val ← finalize val
    (mvarId.assign val : MetaM _)
    return a

  finalize (val : Expr) : MetaM Expr := do
    trace[grind.debug.proof] "{val}"
    let type ← inferType val
    -- `grind` proofs are often big, if `abstractProof` is true, we create an auxiliary theorem.
    let val ← if !config.abstractProof then
      pure val
    else if (← isProp type) then
      mkAuxTheorem type val (zetaDelta := true)
    else
      let auxName ← mkAuxDeclName `grind
      mkAuxDefinition auxName type val (zetaDelta := true)
    return val

end Lean.Meta.Grind
