/-
Copyright (c) 2026 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez
-/
module

prelude
public import Lean.Elab.PreDefinition
public import Lean.Elab.Deriving.Basic
public import Lean.Meta.Constructions.CtorIdx
public import Lean.Meta.Constructions.CtorElim

public section

open Lean Meta Elab Command Term

set_option linter.missingDocs true

/--
Force all delayed assigned variables to be assigned if possible even if the assignment would
contain metavariables. The reason we need this function is that abstracting metavariables using
`mkLambdaFVars` / `mkForallFVars` doesn't work well with delayed assigned metavariables. Example:
```
open Lean Meta
run_meta
  let mvar ← mkFreshExprSyntheticOpaqueMVar Nat.mkType `n
  withLocalDeclD `m Nat.mkType fun var => do
    let goal ← mkFreshExprSyntheticOpaqueMVar Nat.mkType `goal
    let res ← mkLambdaFVars #[var] goal
    goal.mvarId!.assign (mkNatAdd mvar var)
    -- we want `fun n m => n + m` but we get `fun n m => ?goal`
    logInfo <| ← mkLambdaFVars #[mvar] res (binderInfoForMVars := .default)
    -- `instantiateMVars` doesn't help
    logInfo <| ← mkLambdaFVars #[mvar] (← instantiateMVars res) (binderInfoForMVars := .default)
    -- `forceProcessDelayedAssignments` + `instantiateMVars` *does* help
    forceProcessDelayedAssignments
    logInfo <| ← mkLambdaFVars #[mvar] (← instantiateMVars res) (binderInfoForMVars := .default)
```
We use this function in the `Meta.Deriving` framework because it uses synthetic opaque
metavariables for instance binders.
-/
partial def Lean.Meta.forceProcessDelayedAssignments : MetaM Unit := do
  let mut progress := true
  -- Note: we run this in a loop because `mkLambdaFVars` and this function itself can also add
  -- normal and delayed assignments
  while progress do
    -- for cancellation, since nothing else calls it here
    -- and under bad circumstances (assignment loops), this might go into an infinite loop
    -- so better fail with heartbeat exhaustion than go on forever
    checkSystem "forceProcessDelayedAssignments"
    progress := false
    let mctx ← getMCtx
    for (mvar, dassignment) in mctx.dAssignment do
      if ← mvar.isAssigned then
        -- prune the delayed assignment table to make sure that later iterations go faster
        -- ideally, the second iteration ends up with an empty delayed assignment table
        modifyMCtx fun mctx => { mctx with dAssignment := mctx.dAssignment.erase mvar }
        continue
      if let some eassignment ← getExprMVarAssignment? dassignment.mvarIdPending then
        dassignment.mvarIdPending.withContext do
          mvar.assign (← mkLambda dassignment.fvars eassignment)
        modifyMCtx fun mctx => { mctx with dAssignment := mctx.dAssignment.erase mvar }
        progress := true
where
  /--
  `MetavarContext.MkBinding.mkBinding` specialized for always generating lambdas. In the presence
  of let declarations, the resulting expression may only be type correct after beta reduction with
  the free variables.
  -/
  mkLambda (xs : Array Expr) (e : Expr) : MetaM Expr := do
    let lctx ← getLCtx
    let e ← e.abstractM xs
    xs.size.foldRevM (init := e) fun i _ e => do
      let x := xs[i]
      let handleCDecl (n : Name) (type : Expr) (bi : BinderInfo) : MetaM Expr := do
        let type ← type.abstractRangeM i xs
        return .lam n type e bi
      match lctx.getFVar! x with
      | LocalDecl.cdecl _ _ n type bi _ =>
        handleCDecl n type bi
      | LocalDecl.ldecl _ _ n type value nondep _ =>
        handleCDecl n type .default

/--
Convenience function for creating and registering an instance declaration with a given name, level
parameters, type and value.

If `isMeta` is true, the instance declaration is marked `meta`; this flag should usually be
inferred either from the context or from the declaration the instance is for.

If the `compile` flag is true, the declaration is compiled unless `type` is a proposition.

For local or scoped instances, use `attrKind := .local` and `attrKind := .scoped` respectively.
You can also set the priority of the instance using e.g. `prio := eval_prio low`.

The instance is exposed whenever possible, i.e. its type is not a proposition, it is not private
and it type checks in the public scope.

In most cases, the instance name should be computed using `mkInstanceNameOfType`.
-/
def Lean.mkInstance (name : Name) (levelParams : List Name) (type value : Expr)
    (isMeta : Bool) (compile : Bool := true) (attrKind : AttributeKind := .global)
    (prio : Nat := eval_prio default) : TermElabM Unit := do
  let isProp ← isProp type
  let decl ←
    if isProp then
      mkThmOrUnsafeDef { name, levelParams, type, value }
    else
      let hints := .regular (getMaxHeight (← getEnv) value + 1)
      pure <| .defnDecl <| ← mkDefinitionValInferringUnsafe name levelParams type value hints
  let mut shouldExport := false
  if isProp then
    -- theorems don't need to be exposed
    shouldExport := false
  else if (← getEnv).isExporting then
    -- in an @[expose] public section, non-prop instances should always be exposed
    shouldExport := true
    prependError m!"Instance `{name}` failed to type check" do
      check value
      let inferred ← inferType value
      unless ← isDefEq inferred type do
        throwTypeMismatchError m!"Declaration type mismatch{indentExpr value}\n" type inferred value
  else if isPrivateName name then
    -- if we already have a private name, we can't expose
    shouldExport := false
  else
    -- otherwise, we type check the expression in the public scope
    shouldExport ← withExporting <|
      isTypeCorrect value <&&> (do isDefEq (← inferType value) type)
  withExporting (isExporting := shouldExport) do
    addDecl decl
  unless isProp do
    setReducibilityStatus name .instanceReducible
  addInstance name attrKind prio
  if isMeta && !isProp then
    modifyEnv (markMeta · name)
  unless isProp do
    if compile then
      compileDecl decl (logErrors := !(← read).isNoncomputableSection || isMeta)
    else
      modifyEnv (addNoncomputable · name)
  enableRealizationsForConst name
  addDeclarationRangesFromSyntax name (← getRef)

namespace Lean.Meta.Deriving

/--
If true, use instance requirements verbatim as instance binders instead of trying to synthesize
them while deriving instances. Example:
```
set_option deriving.bindersVerbatim true in
structure Test where
  value : Nat
deriving BEq

/-- info: instBEqTest [BEq Nat] : BEq Test -/
#guard_msgs in #check instBEqTest
```

Note: This option only affects deriving handlers that support it, i.e. deriving handlers that use
the `Lean.Meta.Deriving` framework.
-/
register_builtin_option deriving.bindersVerbatim : Bool := {
  defValue := false
  descr := "if true, use instance requirements verbatim as instance binders instead of trying to \
    synthesize them in deriving handlers"
}

/--
If true, reduce instance requirements in deriving handlers by applying instances. Example:
```
set_option deriving.reduceInstances false in
structure TestWithout (α : Type) where
  value : List α
deriving BEq

set_option deriving.reduceInstances true in -- default
structure TestWith (α : Type) where
  value : List α
deriving BEq

/-- info: instBEqTestWithout (α : Type) [BEq (List α)] : BEq (TestWithout α) -/
#guard_msgs in #check instBEqTestWithout

/-- info: instBEqTestWith (α : Type) [BEq α] : BEq (TestWith α) -/
#guard_msgs in #check instBEqTestWith
```

Note: This option only affects deriving handlers that support it, i.e. deriving handlers that use
the `Lean.Meta.Deriving` framework.
-/
register_builtin_option deriving.reduceInstances : Bool := {
  defValue := true
  descr := "if true, reduce instance hypotheses like `BEq (List α)` to `BEq α` in deriving handlers"
}

/--
If true, raise an error in deriving handlers if it would generate an instance with
instance hypotheses that are not simple.

An instance hypothesis is deemed simple if its type contains no other constants except the
class name, projections, instances, instance projections, proofs and `Eq`, and also doesn't contain
other special expressions (foralls, universes, lambdas) after unfolding reducible declarations.

For example, `BEq α`, `DecidableEq α`, `DecidableLE α` and `Repr params.1` are accepted by this
check but `BEq MyType`, `DecidableEq Prop` or `Repr (Nat → Nat)` are not.

The check is omitted even with `deriving.strict` enabled if `deriving.bindersVerbatim` is enabled
or `deriving.reduceInstances` is disabled.

Note: This option only affects deriving handlers that support it, i.e. deriving handlers that use
the `Lean.Meta.Deriving` framework.
-/
register_builtin_option deriving.strict : Bool := {
  defValue := true
  descr := "if true, reject complex instance hypotheses in deriving handlers"
}

/--
If true, in cases where a deriving handler would usually expect there to be exactly one matching
instance declaration, choose the last one with the highest priority (the one that would be tried
first by instance synthesis).

This currently happens in two scenarios: First, when `deriving.reduceInstances` is enabled,
instances are usually only applied when they are the only suitable one. For example, when a
deriving handler requires a `BEq (Option α)` hypothesis, it would usually be split into `BEq α`.
But if there were two instance declarations for `BEq (Option α)`, it would fail unless this option
is enabled.

Second, when deriving a law type class (e.g. `ReflBEq` for `BEq`), the deriving handler checks that
there is only one instance of the original type class unless this option is enabled.

Note: This option only affects deriving handlers that support it, i.e. deriving handlers that use
the `Lean.Meta.Deriving` framework.
-/
register_builtin_option deriving.chooseArbitraryInstance : Bool := {
  defValue := false
  descr := "if true, choose an arbitrary instance when only one would usually be expected \
    in deriving handlers"
}

/--
If true, always use implicit binders instead of explicit binders for instances generated by
deriving handlers. Otherwise, the binder infos will simply be inferred from the inductive.

Note: This option only affects deriving handlers that support it, i.e. deriving handlers that use
the `Lean.Meta.Deriving` framework.
-/
register_builtin_option deriving.implicitBinders : Bool := {
  defValue := true
  descr := "if true, use implicit binders for instances generated by deriving handlers"
}

/--
If true, derive multiple instances for the same type if needed to cover all universe possibilities.

For example, with this option enabled, deriving an instance of a type class of the shape
`MyClass (α : Type u)` for a type of the shape `MyType (α : Sort u) : Sort (max 1 u)` will
generate two instances: One for `MyClass (MyType.{0} α)` with `α : Prop` and one for
`MyClass (MyType.{u + 1} α)` with `α : Type u`. With the option disabled, only the `α : Type u`
variant will be generated, leaving no instance for `MyClass (MyType True)`.

Because the number of needed instances can be exponential in the number of universe parameters,
deriving handlers will usually fail if there are more than 8 possible instantiations of universe
parameters. This limit is controlled by the `deriving.univPoly.limit` option.

Note: This option only affects deriving handlers that support it, i.e. deriving handlers that use
the `Lean.Meta.Deriving` framework.
-/
register_builtin_option deriving.univPoly : Bool := {
  defValue := true
  descr := "if true, derive multiple instances if needed to cover all universe possibilities"
}

/--
The maximum number of instantiations of universe parameters that deriving handlers are allowed to
process. If the limit is positive, any greater number of universe instantiations will cause the
deriving handler to fail. `0` means "no limit".

See the `deriving.univPoly` option for more information.

Note: This option only affects deriving handlers that support it, i.e. deriving handlers that use
the `Lean.Meta.Deriving` framework.
-/
register_builtin_option deriving.univPoly.limit : Nat := {
  defValue := 8
  descr := "limit for the deriving.univPoly option"
}

private def isIgnoredConstant (nm : Name) (env : Environment) : Bool :=
  nm == ``Eq || (env.getProjectionFnInfo? nm).any (·.fromClass)

/-
TODO: better heuristics for `goodKeys` and `goodHypothesisKeys`

The current heuristic is that we only apply instances with keys of the shape
`ClassName ... TypeName ...` where `...` consists only of `.star` placeholders, instance
projections, `Eq` or duplicate mentions of `TypeName`. This particular choice of heuristic is
guided by the typical shape of instances for types, which would be
`ClassName (TypeName variables...)`.

We need to ignore `Eq` here because of `DecidableEq`, which has the shape
`Decidable (@Eq (TypeName ...) ...)` instead and instance projections and duplicates because of
e.g. `ReflOrd` which has the shape `@ReflCmp (TypeName ...) (@compare (TypeName ...) ...)`.

However, it is not entirely clear whether this is a good heuristic. Ideally, we would want to apply
exactly those instances that are always safe to apply (i.e. when such an instance matches against
the instance type `X = ClassName ...`, and `X` is synthesizable, then `X` is also synthesizable
through that instance). However, this property is in general undecidable and can change when new
instances are added.
-/

private def goodKeys (keys : Array DiscrTree.Key) (env : Environment) : Bool := Id.run do
  let some (.const _ _) := keys[0]? | return false
  let mut specialFragment : Option DiscrTree.Key := none
  for h : i in 1...keys.size do
    let key := keys[i]
    match key with
    | .const nm _ =>
      if isIgnoredConstant nm env then
        continue
      if specialFragment.isSome && !specialFragment.isEqSome key then
        return false
      specialFragment := some key
    | .arrow =>
      if specialFragment.isSome && !specialFragment.isEqSome key then
        return false
      specialFragment := some key
    | .star => continue
    | _ => return false
  return specialFragment.isSome

private def goodHypothesisKeys (keys : Array DiscrTree.Key) (env : Environment) : Bool := Id.run do
  let some (.const _ _ : DiscrTree.Key) := keys[0]? | return false
  return keys.all (start := 1) fun key =>
    match key with
    | .star => true
    | .proj .. => true
    | .fvar .. => true
    | .const nm _ => isIgnoredConstant nm env
    | _ => false

/-- The error type for the internal function `tryApplyCanonicalInstance` -/
inductive CanonicalInstanceFailure where
  /-- There are no suitable instances or at least two successful matches -/
  | nonUnique (matching filtered : Array InstanceEntry)
  /-- Unification of the goal with the instance type failed -/
  | unifyFailed (instEntry : InstanceEntry)
  /--
  After unification, some part of the result has metavariables:
  * an argument if `isArg = true`
  * the resulting instance if `isArg = false`
  -/
  | hasMVars (mctx : MetavarContext) (instEntry : InstanceEntry) (e : Expr) (isArg : Bool)
  /-- Multiple instances were tried and all failed -/
  | multi (xs : Array CanonicalInstanceFailure)
deriving Inhabited

/-- Whether we failed because of no suitable matching instances -/
def CanonicalInstanceFailure.isNoMatch : CanonicalInstanceFailure → Bool
  | .nonUnique _ filtered => filtered.isEmpty
  | _ => false

/-- Whether we failed because of multiple successes -/
def CanonicalInstanceFailure.isMultiMatch : CanonicalInstanceFailure → Bool
  | .nonUnique _ filtered => filtered.size > 1
  | _ => false

/-- Turn the failure into a nice error message -/
partial def CanonicalInstanceFailure.toMessageData : CanonicalInstanceFailure → MetaM MessageData
  | .nonUnique matching filtered =>
    if matching.isEmpty then
      return "No matching instances"
    else if filtered.isEmpty then
      if let #[single] := matching then
        return m!"The instance {single.val} matched but did not have the right shape to be considered"
      else
        return m!"The instances {.andList (matching.map (·.val)).toList} matched but none of them \
          had the right shape to be considered"
    else
      return m!"There were multiple instance candidates: {.andList (filtered.map (·.val)).toList}"
  | .unifyFailed instEntry => return m!"Failed to unify with the conclusion of {instEntry.val}"
  | .hasMVars mctx instEntry e isArg =>
    withMCtx mctx do
      addMessageContext m!"After unifying with the conclusion of {instEntry.val}, \
        the {if isArg then "argument" else "instance application"}{indentExpr e}\n\
        still contained unexpected {if e.hasLevelMVar then "level " else ""}metavariables"
  | .multi errors => do
    return m!"Every applicable instance failed to match:\
      {indentD <| MessageData.joinSep (← errors.toList.mapM toMessageData) "\n"}"

/--
Filters `possible` for instances that are not erased and available in the environment.
-/
private def filterActiveInstances (possible : Array InstanceEntry) :
    CoreM (Array InstanceEntry) := do
  let erasedInstances ← getErasedInstances
  let env ← getEnv
  return possible.filter fun entry => entry.globalName?.any <| fun constName =>
    !erasedInstances.contains constName && (!env.isExporting || env.contains constName)

/--
Without `deriving.chooseArbitraryInstance`, returns `some 0` if `possible` has exactly one element
and `none` if it has no elements or more than one. Otherwise, returns the index of the last
instance with the highest priority or `none` if `possible` is empty.
-/
private def chooseInstance (possible : Array InstanceEntry)
    : CoreM (Option (Fin possible.size)) := do
  if h : possible.size = 0 then
    return none
  else if h : possible.size = 1 then
    return some ⟨0, by omega⟩
  else
    unless deriving.chooseArbitraryInstance.get (← getOptions) do
      return none
    let mut bestIdx : Fin possible.size := ⟨0, by omega⟩
    let mut best := possible[0]
    for h : i in 1...possible.size do
      let inst := possible[i]
      if best.priority ≤ inst.priority then
        bestIdx := ⟨i, h.2⟩
        best := inst
    return bestIdx

/--
Given an instance type `instType`, try to apply a canonical instance, producing new instance
hypotheses as synthetic opaque metavariables.

The result of this function is a pair of the instance application and the list of new instance
hypotheses together with an indication of whether to run this function again on the resulting
instance obligation. We use a heuristic here to (try to) make sure we don't run into an infinite
loop.

Canonical instances are currently defined as instances with exactly two special fragments in the
discrimination tree keys (forall and constants except `Eq` and instance projections because of
`DecidableEq` and e.g. `TransOrd`). Furthermore, we only accept an instance if it is the only one
with "good keys" that matches the `instType` (unless `deriving.chooseArbitraryInstance` is true).
-/
private def tryApplyCanonicalInstance (instType : Expr) :
    MetaM (Except CanonicalInstanceFailure (Expr × Array (MVarId × Bool))) := do
  let lctx ← getLCtx
  let linsts ← getLocalInstances
  let state ← (saveState : MetaM _)
  forallTelescopeReducing (whnfType := true) instType fun vars body => do
    -- try to apply instance
    let instances ← getGlobalInstancesIndex
    let matching ← instances.getUnify body
    let env ← getEnv
    let matching ← filterActiveInstances matching
    let filtered := matching.filter fun inst => goodKeys inst.keys env
    let mut successes : Array (InstanceEntry × SavedState × Expr × Array (MVarId × Bool)) := #[]
    let mut failures : Array CanonicalInstanceFailure := #[]
    for instEntry in filtered do
      -- try each one with the initial state
      state.restore
      let res ← tryInstance instEntry body
      match res with
      | .ok (inst, subgoals) =>
        successes := successes.push (instEntry, ← (saveState : MetaM _), inst, subgoals)
      | .error failure =>
        failures := failures.push failure
    if successes.isEmpty && !failures.isEmpty then
      if h : failures.size = 1 then
        return .error failures[0]
      else
        return .error (.multi failures)
    -- we only consider successes for duplicates
    -- this is in particular important if there are many instances that only differ in level
    -- parameters, like with `deriving.univPoly true`
    let some idx ← chooseInstance (successes.map (·.1))
      | return .error (.nonUnique matching filtered)
    let (_, state, res, outVars) := successes[idx]'(by simpa using idx.2)
    state.restore
    let mut outVars : Array (MVarId × Bool) := outVars
    -- If we have additional variables from `forallTelescopeReducing` here, we have to revert them
    unless vars.isEmpty do
      outVars ← outVars.mapM fun (outVar, allowMore) => do
        let mvarApp ← mkFreshRevertedMVarAt lctx linsts (← outVar.getType)
        outVar.assign mvarApp
        return (mvarApp.getAppFn.mvarId!, allowMore)
    trace[Elab.Deriving] "Result: {res}, {outVars}"
    return .ok (← mkLambdaFVars vars res, outVars)
where
  tryInstance (instEntry : InstanceEntry) (body : Expr)
      : MetaM (Except CanonicalInstanceFailure (Expr × Array (MVarId × Bool))) := do
    let some name := instEntry.globalName? | unreachable!
    let c ← mkConstWithFreshMVarLevels name
    let (args, bis, instBody) ← forallMetaTelescopeReducing (← inferType c)
    let mut outVars := #[]
    for arg in args, bi in bis do
      if bi.isInstImplicit then
        if instBody.containsMVar arg.mvarId! then
          continue
        let argType ← inferType arg
        let keys ← withoutModifyingMCtx do
          let (_, _, body) ← forallMetaTelescopeReducing argType
          DiscrTree.mkPath body
        arg.mvarId!.setKind .syntheticOpaque
        outVars := outVars.push (arg.mvarId!, goodHypothesisKeys keys (← getEnv))
    unless ← withReducibleAndInstances <| isDefEq instBody body do
      return .error (.unifyFailed instEntry)
    let c ← instantiateMVars c
    if c.hasLevelMVar then
      return .error (.hasMVars (← getMCtx) instEntry c (isArg := false))
    let mctx ← getMCtx
    let mut res := c
    for arg in args do
      let arg ← instantiateMVars arg
      -- all metavariables that were there before should be synthetic opaque
      if arg.hasLevelMVar then
        return .error (.hasMVars mctx instEntry arg (isArg := true))
      if arg.hasAnyMVar (fun m => !(mctx.getDecl m).kind.isSyntheticOpaque) then
        return .error (.hasMVars mctx instEntry arg (isArg := true))
      res := res.app arg
    return .ok (res, outVars)

/-- The state of the `DerivingM` monad -/
structure State where
  /-- Metavariables for potential instance binders created by `synthInstanceDeriving` -/
  instanceMVars : Array MVarId := #[]
  /-- Local instances associated to `instanceMVars` -/
  newLInsts : LocalInstances := #[]
  /-- There are exactly as many local instances as instance metavariables -/
  invariant1 : instanceMVars.size = newLInsts.size := by rfl
  /-- Each local instance has the corresponding metavariable as the value -/
  invariant2 (i : Nat) (hi : i < newLInsts.size) :
    newLInsts[i].fvar = .mvar instanceMVars[i] := by nofun
  /--
  Failures of the internal `tryApplyCanonicalInstance` function associated to instance
  metavariables.
  -/
  splitFailures : Array (MVarId × CanonicalInstanceFailure) := #[]

/-- The context for the `DerivingM` monad -/
structure Context where
  /-- The name of the type class being derived -/
  className : Name
  /-- Level parameters for the instances -/
  levelParams : List Name
  /-- Free variables for instance parameters -/
  params : Array Expr
  /-- The local context that contains all `params` -/
  paramLCtx : LocalContext
  /-- The local instances for `paramLCtx` -/
  paramLInsts : LocalInstances
  /-- One inductive in the mutual group -/
  indInfo : InductiveVal
  /-- Level parameters for the inductive type -/
  indLParams : List Level
  /--
  Parameters (and potentially indices) for the inductive type. By default, this coincides with
  `params` but this doesn't have to be the case in general. These have to type-check in `paramLCtx`.
  -/
  indParams : Array Expr
  /--
  The resulting level for the mutual inductive type, i.e.
  `mkAppN (mkAppN (.const indInfo.name indLParams) indParams) indIndices : Sort indLevel`
  for any valid `indIndices`. In the case of `mkInductiveDerivingHandler`, this is guaranteed to
  match the level shape provided to the function (or inferred by `inferLevelShape`).
  -/
  indLevel : Level
  /--
  The names of the declarations within `indInfo.all` that we should generate instances for.
  -/
  names : Array Name
  /-- `names` as a `NameSet`. -/
  nameSet : NameSet := .ofArray names
  /--
  Whether the generated instances should be `meta`.
  -/
  isMeta : Bool

/--
The `DerivingM` monad builds on top of `TermElabM` with context about what is being derived and
potential instance binders as state.

The key operations provided by `DerivingM` are:
* `synthInstanceDeriving`, which tries to synthesize an instance and adds missing instances as
  potential instance binders
* `produceInstanceHyps`, which filters the potential instance binders into a suitable list of
  metavariable instance binders
-/
abbrev DerivingM := ReaderT Deriving.Context <| StateRefT Deriving.State TermElabM

instance : Inhabited (DerivingM α) where
  default := liftM (default : TermElabM α)

/-- Run a `DerivingM` computation with the given context -/
nonrec def DerivingM.run (x : DerivingM α) (ctx : Deriving.Context) : TermElabM α :=
  (x.run ctx).run' {}

private def pushInstanceHypothesis (type : Expr) (className : Name) (allLInsts : LocalInstances)
    : DerivingM (Expr × LocalInstances) := do
  -- We simply add the new metavariables as local instances for instance synthesis to pick up
  -- That way we can detect redundant instances more easily
  let mvarApp ← mkFreshRevertedMVarAt (← read).paramLCtx (← read).paramLInsts type
  let goal := mvarApp.getAppFn.mvarId!
  let linst := { className, fvar := .mvar goal }
  modify fun state => {
    state with
    instanceMVars := state.instanceMVars.push goal
    newLInsts := state.newLInsts.push linst
    invariant1 := by simpa using state.invariant1
    invariant2 i hi := by
      have := state.invariant1
      rw [Array.size_push] at hi
      rcases Nat.lt_add_one_iff_lt_or_eq.mp hi with hlt | rfl
      · rw [Array.getElem_push_lt hlt, state.invariant2 i hlt, Array.getElem_push_lt (by omega)]
      · rw [Array.getElem_push_eq, Array.getElem_push, dite_eq_right (by omega)]
  }
  return (mvarApp, allLInsts.push linst)

/--
Returns true if `e` contains any reference to inductives from the mutual block being operated on.
-/
def containsRecursiveDecl (e : Expr) : DerivingM Bool := do
  let ctx ← read
  let all := ctx.indInfo.all
  return (e.find? fun | .const nm _ => nm ∈ all | _ => false).isSome

private def trySynthesize (type : Expr) (allLInsts : LocalInstances) : DerivingM (Option Expr) := do
  unless deriving.bindersVerbatim.get (← getOptions) do
    let .some inst ← withLCtx (← getLCtx) allLInsts <| trySynthInstance type | return none
    if inst.hasLevelMVar then return none
    return inst
  let some className ← isClass? type |
    throwError "type class instance expected{indentExpr type}"
  forallTelescope type fun vars body => do
    for inst in allLInsts do
      if inst.className == className then
        let state ← (saveState : MetaM _)
        let (instArgs, _, res) ← forallMetaTelescope (← inferType inst.fvar)
        if ← withReducibleAndInstances <| isDefEq res body then
          let instArgs ← instArgs.mapM instantiateMVars
          let mctx ← getMCtx
          if instArgs.any (·.hasAnyMVar (fun m => !(mctx.getDecl m).kind.isSyntheticOpaque)) then
            state.restore
            continue
          return ← mkLambdaFVars (etaReduce := true) vars (mkAppN inst.fvar instArgs)
        state.restore
    return none

/--
Given `allLInsts = (← getLocalInstances) ++ (← get).newLInsts`, returns
`(inst : type, newAllLInsts)` (we may add instances during the process that should be
picked up by later calls of `synthInstanceDerivingAux`).
-/
private partial def synthInstanceDerivingAux (type : Expr) (allLInsts : LocalInstances)
    (allowCanonicalInstanceReduction : Bool := true) :
    DerivingM (Expr × LocalInstances) := withIncRecDepth do
  let some className ← isClass? type |
    throwError "type class instance expected{indentExpr type}"
  if let some res ← trySynthesize type allLInsts then
    return (res, allLInsts)
  let mut shouldTry := allowCanonicalInstanceReduction -- avoid loops
  if !deriving.reduceInstances.get (← getOptions) ||
      deriving.bindersVerbatim.get (← getOptions) then
    shouldTry := false
  unless shouldTry do
    -- if the instance requirement is nested (i.e. contains recursive occurrences),
    -- we *have* to reduce it, otherwise we end up with a useless instance like
    -- `instance [BEq (List Thing)] : BEq Thing`
    unless ← containsRecursiveDecl type do
      return ← pushInstanceHypothesis type className allLInsts
    -- also, try instance synthesis even if it was disabled through `deriving.bindersVerbatim`
    if let .some res ← withLCtx (← getLCtx) allLInsts <| trySynthInstance type then
      return (res, allLInsts)
  -- try reducing e.g. `BEq (List α)` to `BEq α`
  let res ← tryApplyCanonicalInstance type
  match res with
  | .ok (assignment, outVars) =>
    let mut allLInsts := allLInsts
    for (var, allow) in outVars do
      let (res, newAllLInsts) ← synthInstanceDerivingAux (← var.getType) allLInsts allow
      var.assign res
      allLInsts := newAllLInsts
    return (← instantiateMVars assignment, allLInsts)
  | .error e =>
    if ← containsRecursiveDecl type then
      throwError "Got stuck at instance requirement for nested type while deriving an \
        instance for {.ofConstName (← read).className}:{indentExpr type}\n\
        Reason: {← e.toMessageData}"
    let res ← pushInstanceHypothesis type className allLInsts
    let mvar := res.1.getAppFn.mvarId!
    modify fun state => { state with splitFailures := state.splitFailures.push (mvar, e) }
    return res

/--
Try synthesizing an instance of type `e`, adding instance binders if the instance can't be
synthesized directly.

The expression provided should not contain metavariables except ones returned by this function;
there is no support for `outParam`s.
-/
def synthInstanceDeriving (e : Expr) : DerivingM Expr := do
  let mctx ← getMCtx
  let e ← instantiateMVars e
  if e.hasAnyMVar (fun m => !(mctx.getDecl m).kind.isSyntheticOpaque) then
    -- this is an approximation that should catch most cases and is sufficient for the
    -- equivalent check in `tryApplyCanonicalInstance` not to generate false positives
    throwError "Invalid input to `{.ofConstName decl_name%}`, \
      the input expression contains metavariables that were not generated by this function"
  let allLInsts := (← getLocalInstances) ++ (← get).newLInsts
  instantiateMVars <| (← synthInstanceDerivingAux e allLInsts).1

private def blankLInst : LocalInstance where
  className := .anonymous
  fvar := .sort .zero

private structure DepGraph (n : Nat) (inclusive : Bool) where
  transitiveFwdDeps : Vector (Array (Fin n)) n :=
    if inclusive then
      Vector.ofFn fun i : Fin n => #[i]
    else
      Vector.replicate n #[]
  directBackDeps : Vector (Array (Fin n)) n := Vector.replicate n #[]

/-- Record that `i` depends on `j` -/
private partial def DepGraph.recordDep
    (d : DepGraph n inc) (i j : Fin n) : DepGraph n inc :=
  let d := { d with directBackDeps := d.directBackDeps.modify i (insert · j) }
  goFwd j d
where
  insert (xs : Array (Fin n)) (i : Fin n) : Array (Fin n) :=
    -- we often add things in order
    match xs.back? with
    | none => #[i]
    | some j =>
      if j < i then xs.push i else if j = i then xs else xs.binInsert (· < ·) i
  goFwd (j : Fin n) (d : DepGraph n inc) : DepGraph n inc :=
    let prevSz := d.transitiveFwdDeps[j].size
    let d := { d with transitiveFwdDeps := d.transitiveFwdDeps.modify j (insert · i) }
    if d.transitiveFwdDeps[j].size = prevSz then
      d -- already registered
    else
      d.directBackDeps[j].foldl (init := d) fun d j' => goFwd j' d

private partial def DepGraph.topoSort (d : DepGraph n inc) : Array (Fin n) :=
    Id.run <| StateT.run' (s := 0) do
  Fin.foldlM n visit #[]
where
  visit (acc : Array (Fin n)) (i : Fin n) : StateM Nat (Array (Fin n)) := do
    if (← get).testBit i then
      return acc
    else
      modify fun visited => visited ||| 1 <<< i.val
      let mut acc := acc
      for dep in d.directBackDeps[i] do
        acc ← visit acc dep
      return acc.push i

/--
Given a list of metavariables corresponding to instance obligations, eliminate redundant instances,
returning a suitable list of instance assumptions to be used in
`mkLambdaFVars (binderInfoForMVars := .instImplicit)`.

Precondition: The current local context must also be the local context of all metavariables.
-/
private def filterInstanceObligations (state : Deriving.State) : MetaM (Array MVarId) := do
  if deriving.bindersVerbatim.get (← getOptions) then
    return state.instanceMVars
  let n := state.instanceMVars.size
  let mut idxOfMVar : MVarIdMap (Fin n) := {}
  for h : i in 0...n do
    idxOfMVar := idxOfMVar.insert state.instanceMVars[i] ⟨i, h.2⟩
  let mut depGraph : DepGraph n (inclusive := true) := {}
  for h : i in 0...n do
    let deps ← state.instanceMVars[i].getMVarDependencies
    for dep in deps do
      let some j := idxOfMVar.get? dep | continue
      depGraph := depGraph.recordDep ⟨i, h.2⟩ j
  let linsts ← getLocalInstances
  let lctx ← getLCtx
  let allLInsts := linsts ++ state.newLInsts
  let m := allLInsts.size
  have : state.newLInsts.size ≤ m := by unfold m allLInsts; simp
  let mut oldLInsts : Vector LocalInstance m := ⟨allLInsts, rfl⟩
  let mut newLInsts : Vector LocalInstance m := ⟨allLInsts, rfl⟩
  have := state.invariant1
  for h : i in 0...n do
    have h : i < n := h.2
    -- disable local instance for itself and mvars that depend on it
    for dep in depGraph.transitiveFwdDeps[i] do
      newLInsts := newLInsts.set (dep + m - n) blankLInst
    let mvar := state.instanceMVars[i]
    let mvarType ← mvar.getType
    if let .some res ← withLCtx lctx newLInsts.toArray (trySynthInstance mvarType) then
      -- add new dependencies
      mvar.assign res
      let deps ← res.getMVarDependencies
      for dep in deps do
        let some j := idxOfMVar.get? dep | continue
        depGraph := depGraph.recordDep ⟨i, h⟩ j
    -- restore the local instances
    for dep in depGraph.transitiveFwdDeps[i] do
      newLInsts := newLInsts.set (dep + m - n) oldLInsts[dep + m - n]
  let mut newMVars := #[]
  for i in depGraph.topoSort do
    let mvar := state.instanceMVars[i]
    if ← mvar.isAssigned then
      continue
    mvar.setType (← instantiateMVars (← mvar.getType))
    newMVars := newMVars.push mvar
  return newMVars

private def checkInstanceHypotheses (instanceHyps : Array MVarId) : DerivingM Unit := do
  let mut complexHyps : Array (Expr × Option CanonicalInstanceFailure) := #[]
  for mvar in instanceHyps do
    let type ← mvar.getType
    withReducible do←
    forallTelescopeReducing type (whnfType := true) fun _ body => do←
      let path ← DiscrTree.mkPath body
      unless goodHypothesisKeys path (← getEnv) do
        let reason? := ((← get).splitFailures.find? (·.1 == mvar)).map (·.2)
        complexHyps := complexHyps.push (type, reason?)
  unless complexHyps.isEmpty do
    let mut msg := m!"While deriving an instance for {.ofConstName (← read).className}, the \
      following complex instance requirements were encountered that could not be synthesized:"
    for (type, reason?) in complexHyps do
      if let some reason := reason? then
        msg := msg ++ indentD (type ++ ", reason:" ++ indentD (← reason.toMessageData))
      else
        msg := msg ++ indentD type
    if complexHyps.any (·.2.any (·.isNoMatch)) then
      msg := msg ++ .hint' m!"You may be able to derive the missing instance using the syntax \
        `deriving instance ClassName for TypeName`."
    if complexHyps.any (·.2.any (·.isMultiMatch)) then
      msg := msg ++ .hint' m!"Having multiple instance candidates usually indicates that one of \
        the mentioned instances is redundant. If this is intentional though, you can make the \
        deriving handler choose an instance using \
        `set_option {deriving.chooseArbitraryInstance.name} true`."
    msg := msg ++ .hint' m!"If you want to keep these hypotheses as-is, you can disable \
      this error using `set_option {deriving.strict.name} false`"
    throwError msg

/--
Returns a list of metavariables to be used as instance binders.

After instantiating metavariables, every metavariable in expressions produced by
`synthInstanceDeriving` will be contained in this output. This makes it possible to use them in
`mkLambdaFVars` and `mkForallFVars` with `binderInfoForMVars := .instImplicit` in combination with
`instantiateMVars` on expressions containing instances generated from `synthInstanceDeriving`.
Alternatively, they can be used directly in the convenience function `mkInstanceForDeriving`.
-/
def produceInstanceHyps : DerivingM (Array Expr) := do
  let filtered ← withLCtx (← read).paramLCtx (← read).paramLInsts do
    filterInstanceObligations (← get)
  if deriving.strict.get (← getOptions) && !deriving.bindersVerbatim.get (← getOptions) &&
      deriving.reduceInstances.get (← getOptions) then
    checkInstanceHypotheses filtered
  return filtered.map Expr.mvar

/--
Runs `x` without modifying the instance state: Instance binders and metavariables created using
`synthInstanceDeriving` within `withoutModifyingInstanceState` don't persist into the outer scope
and don't affect the result of `produceInstanceHyps` in the outer scope.

This function also resets the metavariable context, including metavariable assignments since
metavariables are used for instance binders generated by `synthInstanceDeriving` and may
be assigned in `produceInstanceHyps`.
-/
@[inline]
def withoutModifyingInstanceState (x : DerivingM α) : DerivingM α := do
  let oldState ← get
  let oldMCtx ← getMCtx
  let oldCache := (← getThe Meta.State).cache
  try
    x
  finally
    set oldState
    modifyThe Meta.State ({ · with cache := oldCache, mctx := oldMCtx })

/--
Convenience function for creating an instance declaration with the given type and value and
instance hypotheses produced by `produceInstanceHyps`. The type and value may depend on any
parameters in the context as well as instances generated by `synthInstanceDeriving`.
-/
def mkInstanceForDeriving (instanceHyps : Array Expr) (type value : Expr)
    (name : Option Name := none) : DerivingM Unit := do
  let allVars := (← read).params ++ instanceHyps
  -- otherwise, `mkLambdaFVars` and `mkForallFVars` don't behave like we want
  forceProcessDelayedAssignments
  let type ← mkForallFVars allVars (← instantiateMVars type) (binderInfoForMVars := .instImplicit)
  let value ← mkLambdaFVars allVars (← instantiateMVars value) (binderInfoForMVars := .instImplicit)
  let instName ← name.getDM (mkInstanceNameOfType type)
  let type := if deriving.implicitBinders.get (← getOptions) then type.explicitToImplicit else type
  mkInstance instName (← read).levelParams type value (← read).isMeta

/-- Returns whether the mutual inductive block being operated on is recursive. -/
def isRecursive : DerivingM Bool := do
  return (← read).indInfo.isRec

/--
Returns whether the mutual inductive block being operated on is nested.
In many cases, you may also want to consider reflexive inductives
(i.e. types with an `α → Induct ...` recurrence). In those cases, use `isNestedOrReflexive`.
-/
def isNested : DerivingM Bool := do
  return (← read).indInfo.isNested

/--
Returns whether the mutual inductive block being operated on is nested or reflexive, i.e.
has complex recurrences like `Array Induct` or `Bool → Induct`.
-/
def isNestedOrReflexive : DerivingM Bool := do
  return (← read).indInfo.isNested || (← read).indInfo.isReflexive

/--
Returns whether the recursors of the mutual inductive block being operated on can only eliminate
into propositions.
-/
def eliminatesToProp : DerivingM Bool := do
  let recInfo ← getConstInfoRec (mkRecName (← read).indInfo.name)
  return recInfo.levelParams.length == (← read).indInfo.levelParams.length

/--
Given `induct ∈ (← read).indInfo.all`, returns an application of `induct` with parameters (but
without indices).
-/
def inductAppWithParams (induct : Name) : DerivingM Expr := do
  return mkAppN (.const induct (← read).indLParams) (← read).indParams

/--
Information for a helper of an instance, parameterized by the type of the result of the
`preHelpers` computation provided to `makeInstancesUsingMutualBlock`
-/
structure HelperInfo (α : Type) where
  /-- Name suffix to add to the name of the instance -/
  suffix : Name
  /-- The type of the helper (without parameters) -/
  type : Expr
  /--
  Given all recursive instances, construct the value for the helper (a value of type `type`).
  The instances are also available in the local context, so most of the time you can just ignore
  the parameter and `synthInstanceDeriving` will pick up on it automatically.

  The additional `α` argument is the result of the `preHelpers` parameter of
  `makeInstancesUsingMutualBlock`; if you don't use `preHelpers`, you can just ignore this
  parameter.
  -/
  mkValue : (instances : Array Expr) → α → DerivingM Expr
  /--
  Function that gets applied to the pre-definition for the helper with the output of
  `produceInstanceHyps` as `instanceHyps`. This can be used to e.g. change the modifiers.
  -/
  postprocess : (instanceHyps : Array Expr) → PreDefinition → MetaM PreDefinition :=
    fun _ p => pure p
deriving Inhabited

/--
Information for an instance, parameterized by the type of the result of the
`preHelpers` computation provided to `makeInstancesUsingMutualBlock`
-/
structure InstanceInfo (α : Type) where
  /-- The inductive for which this instance is generated (used for filtering by `(← read).names`) -/
  induct : Name
  /-- The type of the instance (without parameters) -/
  type : Expr
  /-- The helper declarations to add for this instance -/
  helpers : Array (HelperInfo α)
  /--
  Given (metavariables for) all helpers in order, construct the value of the instance
  (a value of type `type`).
  -/
  mkValue : (helpers : Array Expr) → DerivingM Expr
deriving Inhabited

-- extension of `HelperInfo` and `InstanceInfo` that contain additional information
-- that we compute during `makeInstancesUsingMutualBlock`
private structure ExtendedHelperInfo (α : Type) extends HelperInfo α where
  mvar : Expr
  value : Option Expr := none
  declName : Option Name := none
deriving Inhabited

private structure ExtendedInstanceInfo (α : Type) extends InstanceInfo α where
  extendedHelpers : Array (ExtendedHelperInfo α)
  value : Expr
  fullType : Option Expr := none
  declName : Option Name := none
deriving Inhabited

private structure MakeInstancesState where
  newNames : NameSet := {}

private def MakeInstancesState.avoid : MakeInstancesState → Environment → Name → Bool
  | { newNames }, env, nm => hasNameCollision env nm newNames.contains

private def MakeInstancesState.add : MakeInstancesState → Name → MakeInstancesState
  | { newNames }, nm => { newNames := newNames.insert nm }

/--
Creates instances by first running `preHelpers` with all recursive instances in the local context
and then creating a mutual block with all helpers provided in `infos` (marking declarations as
partial by default) and finally creating all instances individually.

`preHelpers` can be used for one-time computations that only need the instances in scope.
-/
def makeInstancesUsingMutualBlock (infos : Array (InstanceInfo α))
    (preHelpers : DerivingM α := by exact pure ()) : DerivingM Unit :=
  -- We want to keep track of the new declarations we're adding
  -- to make sure we don't have collisions
  StateRefT'.run' (s := {}) <| show StateRefT MakeInstancesState DerivingM Unit from do
  -- 1. create helper mvars and compute instance values
  let infos : Array (ExtendedInstanceInfo α) ← infos.mapM fun info => do
    let extendedHelpers ← info.helpers.mapM fun helper => do
      return { helper with mvar := ← mkFreshExprSyntheticOpaqueMVar helper.type }
    let helperMVars := extendedHelpers.map (·.mvar)
    return { info with extendedHelpers, value := ← info.mkValue helperMVars }
  let instanceValues := infos.map (·.value)
  let instVarInfos := infos.mapIdx fun idx info =>
    ((`recinst).appendIndexAfter (idx + 1), info.type)
  withLocalDeclsDND instVarInfos fun recInsts => do
    let mut infos := infos
    -- 2. run `preHelpers`
    let globalCompute ← preHelpers
    -- 3. compute the helper values
    infos ← infos.mapM fun info => do
      let extendedHelpers ← info.extendedHelpers.mapM fun helper => do
        let mut shouldExport ← pure (← getEnv).isExporting <&&> notM (isProp helper.type)
        let value ← withExporting (isExporting := shouldExport)
          (helper.mkValue recInsts globalCompute)
        let value := (← value.abstractM recInsts).instantiateBetaRevRange
          0 instanceValues.size instanceValues
        return { helper with value }
      return { info with extendedHelpers }
    let instHyps ← produceInstanceHyps
    -- otherwise, `mkLambdaFVars` and `mkForallFVars` don't behave like we want
    forceProcessDelayedAssignments
    -- 4. compute instance types and names
    let allParams := (← read).params ++ instHyps
    infos ← infos.mapM fun info => do
      let mut instType ← instantiateMVars info.type
      instType ← mkForallFVars allParams instType (binderInfoForMVars := .instImplicit)
      if deriving.implicitBinders.get (← getOptions) then
        instType := instType.explicitToImplicit
      let instName ← mkInstanceNameOfType instType (← get).avoid
      modifyThe MakeInstancesState (·.add instName)
      return {
        info with
        fullType := instType
        declName := instName
      }
    -- 5. figure out helper names and assign the helper mvars
    let levelParams := (← read).levelParams
    let lparams := levelParams.map Level.param
    infos ← infos.mapM fun info => do
      let extendedHelpers ← info.extendedHelpers.mapM fun helper => do
        let instName := info.declName.get!
        let declName ← findUnusedName (instName ++ helper.suffix) (← get).avoid
        modifyThe MakeInstancesState (·.add declName)
        let helperRef := mkAppN (.const declName lparams) allParams
        helper.mvar.mvarId!.assign helperRef
        return { helper with declName }
      return { info with extendedHelpers }
    -- 6. abstract helper types and values and instance values
    infos ← infos.mapM fun info => do
      let extendedHelpers ← info.extendedHelpers.mapM fun helper => do
        let type ← instantiateMVars helper.type
        let type ← mkForallFVars allParams type (binderInfoForMVars := .instImplicit)
        let value ← instantiateMVars helper.value.get!
        let value ← mkLambdaFVars allParams value (binderInfoForMVars := .instImplicit)
        trace[Elab.Deriving] "Helper declaration `{helper.declName.get!}` \
          of type{indentExpr type}\nand value{indentExpr value}"
        return { helper with type, value }
      let value ← instantiateMVars info.value
      let value ← mkLambdaFVars allParams value (binderInfoForMVars := .instImplicit)
      trace[Elab.Deriving] "Instance declaration `{info.declName.get!}` \
        of type{indentExpr info.fullType.get!}\nand value{indentExpr value}"
      return { info with extendedHelpers, value }

    -- 7. create all the helper pre-definitions
    let mut helperPredefs : Array PreDefinition := #[]
    let ref ← getRef
    let env ← getEnv
    let isUnsafe := infos.any fun info =>
      env.hasUnsafe info.fullType.get! || env.hasUnsafe info.value ||
        info.extendedHelpers.any fun helper =>
          env.hasUnsafe helper.type || env.hasUnsafe helper.value.get!
    let computeKind := if (← read).isMeta then .meta else .regular
    for info in infos do
      for helper in info.extendedHelpers do
        let predef : PreDefinition := {
          ref, levelParams
          type := helper.type
          value := helper.value.get!
          declName := helper.declName.get!
          kind := if ← isProp helper.type then .theorem else .def
          modifiers := { computeKind, isUnsafe, recKind := .partial }
          binders := .missing
          termination := .none
        }
        helperPredefs := helperPredefs.push (← helper.postprocess instHyps predef)
    -- 8. add the helpers to the environment
    addPreDefinitions ({}, {}) helperPredefs
    for helper in helperPredefs do
      addDeclarationRangesFromSyntax helper.declName (← getRef)
    -- 9. add all instances to the environment
    for info in infos do
      unless (← read).nameSet.contains info.induct do continue
      mkInstance info.declName.get! (← read).levelParams info.fullType.get! info.value (← read).isMeta

/--
Information on how a particular field should be filled in: inline in the instance or using a
helper.
-/
inductive FieldHelperInfo (α : Type) where
  /--
  The field should receive the value inline in the instance. In contrast to `.usingHelper`, that
  means that `e` cannot refer to the other instances recursively.
  -/
  | inline (e : Expr)
  /--
  The field should be computed using an auxiliary function whose value is computed using `mkValue`
  with all recursive instances in context.
  -/
  | usingHelper (mkValue : (instances : Array Expr) → α → DerivingM Expr)

/--
The input to a `FieldHelperProvider` which contains information about a specific field of the type
class being derived.
-/
structure FieldProviderInput where
  /-- The level parameters of the type class -/
  classLParams : List Level
  /-- The parameters of the type class -/
  classParams : Array Expr
  /--
  The application of the inductive type in the mutual block that we are currently deriving an
  instance for; typically a parameter of the type class.
  -/
  typeApp : Expr
  /-- The `ConstantVal` for the field for which a value should be provided -/
  fieldInfo : ConstantVal
  /-- The expected type of the field -/
  expectedType : Expr

/-- The name of the inductive type that we are currently deriving an instance for  -/
@[inline]
def FieldProviderInput.induct (x : FieldProviderInput) : Name :=
  x.typeApp.getAppFn.constName!

/-- The name of the field for which a value should be provided -/
@[inline]
def FieldProviderInput.fieldName (x : FieldProviderInput) : Name :=
  x.fieldInfo.name

/--
A field helper provider provides information on how a field of a type class should be filled given
level parameters for the class, an application of the inductive type to derive an instance for, a
`ConstantVal` for the instance projection function corresponding to the field and the expected type
of the field.
-/
@[expose]
def FieldHelperProvider (α : Type) :=
  (input : FieldProviderInput) → DerivingM (FieldHelperInfo α)

/--
Throws an error explaining that the current field was unhandled. Meant to be used as a catch-all
branch of `makeInstancesUsingCtor` and `InstanceInfo.usingCtor`. See `makeInstancesUsingCtor` for
more information.
-/
def FieldHelperProvider.unhandled : FieldHelperProvider α := fun input => do
  throwError "Internal error in deriving handler for `{.ofConstName <| (← read).className}`:\n\
    Unhandled field `{.ofConstName input.fieldName}`"

/--
Creates a helper that matches on the first argument, calling `perCtor` for each constructor with
the inductive info, constructor info, fields and a constructor application.

The additional `α` argument receives the result of the `preHelpers` computation provided to
`makeInstancesUsingMutualBlock`. If you don't use `preHelpers`, you can simply ignore this
parameter.
-/
def FieldHelperProvider.cases
    (perCtor : InductiveVal → ConstructorVal → Array Expr → Expr → α → DerivingM Expr) :
    FieldHelperProvider α := fun input =>
  return .usingHelper fun _ val => do
    let .forallE _ t tgt _ := input.expectedType
      | throwError "Invalid use of `{.ofConstName decl_name%}`, \
          expected field `{.ofConstName input.fieldName}` to have the shape \
          `α → β` where `α` is the type parameter"
    if t != input.typeApp then
      throwError "Invalid use of `{.ofConstName decl_name%}`, the argument to \
        `{.ofConstName input.fieldName}` is not the type parameter"
    withLocalDeclD `t input.typeApp fun discr => do
      let tgt := tgt.instantiate1 discr
      mkLambdaFVars #[discr] <| ← mkDepCases discr tgt fun ival cval fields ctorApp _tgt => do
        prependError m!"Error while processing constructor {.ofConstName cval.name}:" do
          perCtor ival cval fields ctorApp val

/--
A pair of expressions provided by `foldSimilarVarsParallel`, annotated with information about
dependencies. Note that the types of both expressions may not be equal if `hasBackwardDeps` is
true.
-/
structure ExprPair where
  /-- The universe both sides live in -/
  lvl : Level
  /--
  The type of the left-hand side. As long as `hasBackwardDeps` is false this is also the type of
  the right-hand side.
  -/
  type : Expr
  /--
  The left-hand side. This is guaranteed to be a variable from `leftVars` but may have a different
  type than `rhs`.
  -/
  lhs : Expr
  /--
  The right-hand side. This is not guaranteed to be a variable from `rightVars` because of
  substitution and may also be a new variable. It may have a different type than `lhs` if
  `hasBackwardDeps` is true.
  -/
  rhs : Expr
  /--
  Indicates whether the expression pair has backward dependencies that were not resolved by
  providing an equality proof. As long as all pairs with `hasForwardDeps` provided an equality
  proof this will only be true for variables where `ignoreDep` evaluates to `true`.
  -/
  hasBackwardDeps : Bool
  /--
  Whether this pair has any forward dependencies. If this flag is false then providing an equality
  proof to the continuation has no effect. You should usually prefer using `hasRelevantForwardDeps`
  to check whether to provide an equality proof to the continuation.
  -/
  hasForwardDeps : Bool
  /--
  Whether this pair has any forward dependencies that are not ignored because `ignoreDep` evaluated
  to true for them. If this flag is true, you should try to provide an equality proof to the
  continuation. If you choose to not provide an equality proof to the continuation even if this
  flag is true, `hasBackwardDeps` may end up being true even for variables where `ignoreDep`
  evaluates to false and you should be prepared to handle this case.
  -/
  hasRelevantForwardDeps : Bool

private def mkVarIndexMap (vars : Vector Expr n) : FVarIdMap (Fin n) := Id.run do
  let mut res := {}
  for h : i in 0...n do
    res := res.insert vars[i].fvarId! ⟨i, h.2⟩
  return res

/--
This function assumes that the variables are provided in dependency order, so `i < j` for
`j ∈ fwdDeps[i]`.
-/
private partial def computeFVarDepGraph (vars : Array Expr) :
    MetaM (DepGraph vars.size (inclusive := false)) := do
  let n := vars.size
  let vars : Vector Expr n := vars.toVector
  let mut graph : DepGraph n (inclusive := false) := {}
  -- not necessarily transitive, `j ∈ backDeps[i]` iff `vars[i]` depends directly on `vars[j]`
  let mut backDeps : Array (Array Nat) := Array.emptyWithCapacity vars.size
  let idxOfVar : FVarIdMap (Fin n) := mkVarIndexMap vars
  for h : j in 0...vars.size do
    let var := vars[j]
    let type ← inferType var
    let state := collectFVars {} type
    for var in state.fvarIds do
      if let some i := idxOfVar.get? var then
        unless i < j do
          let fst := indentD m!"vars[{j}] = {vars[j]} : {← inferType vars[j]}"
          let snd := indentD m!"vars[{i}] = {Expr.fvar var} : {← var.getType}"
          throwError "Expected the inputs of `{.ofConstName decl_name%}` to be provided \
            in dependency order but{fst}\ndepends on{snd}"
        graph := graph.recordDep ⟨j, h.2⟩ i
  return graph

/--
Given free variables `leftVars` and `rightVars` such that `mkForallFVars leftVars x` and
`mkForallFVars rightVars x` are syntactically equal for any `x` without free variables, performs a
continuation fold over `leftVars` and `rightVars` in parallel.

The function `f` receives an expression pair, the current state, and a continuation that receives
an optional proof of equality and the new state. You should usually only provide a proof of
equality if `hasRelevantForwardDeps` is true.

Note however that the two expressions provided to `f` may not have the same type although they will
always live in the same universe. Still, it is guaranteed that the types end up the same if all
backward dependencies produced a proof of equality. The best way to ensure that is to always
pass along a proof of equality if `hasRelevantForwardDeps` is true for the pair.

In some cases (commonly, for proofs) you may not even need both expressions to have the same type.
You should note down these cases in `ignoreDep` which takes in the left-hand side variable and its
index in the `leftVars` array. `ignoreDep` affects which pairs have `hasRelevantForwardDeps` true:
A pair has relevant forward dependencies if it has forward dependencies where `ignoreDep` evaluates
to false. If you then always pass along a proof of equality if `hasRelevantForwardDeps` is true,
you guarantee that both sides have the same type unless `ignoreDep` evaluated to true for them.
If you however don't always provide such a proof of equality, you need to be prepared to handle the
case where `hasBackwardDeps` is true (i.e. both sides have potentially different types).

At the end of iteration, `finish` should provide a final value of type `resultType`. The result
type should not depend on any of the variables in `leftVars` and `rightVars`.
-/
def foldSimilarVarsParallel [Monad m] [MonadEnv m] [MonadError m]
    [MonadControlT MetaM m] [MonadLiftT MetaM m]
    (leftVars rightVars : Array Expr) (resultType : Expr)
    (init : σ) (f : ExprPair → σ → (Option Expr → σ → m Expr) → m Expr)
    (finish : σ → m Expr) (ignoreDep : Expr → Nat → m Bool := fun _ _ => pure false) :
    m Expr := do
  let depGraph ← computeFVarDepGraph leftVars
  let allFwdDeps := depGraph.transitiveFwdDeps
  let rec go (i : Nat) (rightVars : Array Expr) (s : σ) : m Expr := do
    if h : i < leftVars.size then
      let lhs := leftVars[i]
      let rhs := rightVars[i]!
      let fwdDeps := allFwdDeps[i]
      let lhsType ← inferType lhs
      let rhsType ← inferType rhs
      let hasBackwardDeps := lhsType != rhsType
      let hasForwardDeps := !fwdDeps.isEmpty
      let hasRelevantForwardDeps ←
        pure hasForwardDeps <&&> fwdDeps.anyM fun j => notM <| ignoreDep leftVars[j] j.val
      let pair : ExprPair := {
        lvl := ← getLevel lhsType
        type := lhsType
        lhs, rhs, hasBackwardDeps, hasForwardDeps, hasRelevantForwardDeps
      }
      f pair s fun proof? s => do
        if proof?.isNone || !hasForwardDeps then
          return ← go (i + 1) rightVars s
        let proof := proof?.get!
        -- Construct an Eq.ndrec term
        let fwdDepVars := fwdDeps.map (rightVars[·]!)
        let motive ← mkForallFVars fwdDepVars resultType
        let motiveSort ← getLevel motive
        let motive ← mkLambdaFVars #[rhs] motive
        forallBoundedTelescope (motive.beta #[lhs]) fwdDeps.size fun newFwdDepVars _ => do
          let mut rightVars := rightVars
          for dep in fwdDeps, newVar in newFwdDepVars do
            rightVars := rightVars.set! dep newVar
          rightVars := rightVars.set! i lhs
          let more ← go (i + 1) rightVars s
          let refl ← mkLambdaFVars newFwdDepVars more
          let ndrecApp := mkApp6 (.const ``Eq.ndrec [motiveSort, pair.lvl])
            lhsType lhs motive refl rhs proof
          let ndrecApp := mkAppN ndrecApp fwdDepVars
          return ndrecApp
    else
      finish s
  go 0 rightVars init

/--
The input of alternatives for `FieldHelperProvider.doubleCases` and
`FieldHelperProvider.doubleCasesSlow` where both sides use the same constructor.
-/
structure SameCtorAlt (α : Type) where
  /-- The `InductiveVal` for the inductive we're matching on -/
  inductInfo : InductiveVal
  /-- The `ConstructorVal` for the constructor of `inductInfo` this alternative is about -/
  ctorInfo : ConstructorVal
  /-- The fields for the constructor on the left-hand side -/
  leftFields : Array Expr
  /-- The fields for the constructor on the right-hand side -/
  rightFields : Array Expr
  /-- The application of `ctorInfo` with parameters and `leftFields` -/
  leftCtorApp : Expr
  /-- The application of `ctorInfo` with parameters and `rightFields` -/
  rightCtorApp : Expr
  /-- The value returned by the `preHelpers` computation or `()` if none was provided -/
  val : α

/--
The input of alternatives for `FieldHelperProvider.doubleCasesSlow` where both sides use different
constructors.
-/
structure DifferentCtorAlt (α : Type) where
  /-- The `InductiveVal` for the inductive we're matching on -/
  inductInfo : InductiveVal
  /-- The `ConstructorVal` for the constructor of `inductInfo` on the left-hand side -/
  leftCtor : ConstructorVal
  /-- The `ConstructorVal` for the constructor of `inductInfo` on the right-hand side -/
  rightCtor : ConstructorVal
  /-- The fields for the constructor on the left-hand side -/
  leftFields : Array Expr
  /-- The fields for the constructor on the right-hand side -/
  rightFields : Array Expr
  /-- The application of `leftCtor` with parameters and `leftFields` -/
  leftCtorApp : Expr
  /-- The application of `rightCtor` with parameters and `rightFields` -/
  rightCtorApp : Expr
  /-- The value returned by the `preHelpers` computation or `()` if none was provided -/
  val : α

/--
A fallback alternative for `FieldHelperProvider.doubleCases` where both sides have provably
different constructor indices.
-/
structure DifferentCtorFallbackAlt (α : Type) where
  /-- The `InductiveVal` for the inductive we're matching on -/
  inductInfo : InductiveVal
  /-- The left-hand side value (a variable) -/
  lhs : Expr
  /-- The right-hand side value (a variable) -/
  rhs : Expr
  /-- A proof that `lhs.ctorIdx ≠ rhs.ctorIdx` -/
  cidxNeProof : Expr
  /-- The value returned by the `preHelpers` computation or `()` if none was provided -/
  val : α

/--
Creates a helper that matches on the first two arguments, calling `sameCtor` for alternatives where
both sides use the same constructor, and `differentCtor` for alternatives where both sides use
different constructors.

The additional `α` argument receives the result of the `preHelpers` computation provided to
`makeInstancesUsingMutualBlock`. If you don't use `preHelpers`, you can simply ignore this
parameter.

Often, the right thing to do for the `sameCtor` branch is to use `foldSimilarVarsParallel` on the
`leftFields` and `rightFields` of the `SameCtorAlt`.

This helper has quadratic complexity due to visiting every pair of constructors. If you don't need
to handle every pair case separately, consider using `FieldHelperProvider.doubleCases` instead.
-/
def FieldHelperProvider.doubleCasesSlow
    (differentCtor : DifferentCtorAlt α → DerivingM Expr)
    (sameCtor : SameCtorAlt α → DerivingM Expr) :
    FieldHelperProvider α := fun input =>
  return .usingHelper fun _ val => do
    let fail := throwError "Invalid use of `{.ofConstName decl_name%}`, \
      expected field `{.ofConstName input.fieldName}` to have the shape \
      `α → α → β` where `α` is the type parameter"
    let .forallE _ ty (.forallE _ ty' tgt _) _ := input.expectedType | fail
    unless ty == input.typeApp do return ← fail
    unless ty' == input.typeApp do return ← fail
    if tgt.hasFVar || tgt.hasLooseBVars then
      throwError "Invalid use of `{.ofConstName decl_name%}`, the target type for \
        `{.ofConstName input.fieldName}` depends on the type parameter or the field arguments"
    withLocalDeclD `lhs input.typeApp fun lhs => do
    withLocalDeclD `rhs input.typeApp fun rhs => do
      mkLambdaFVars #[lhs, rhs] <|
        ← mkNondepCases lhs tgt fun ival cval fields ctorApp => do
        mkNondepCases rhs tgt fun _ival cval' fields' ctorApp' => do
          prependError m!"Error while processing constructor pair \
              {.ofConstName cval.name}, {.ofConstName cval'.name}:" do
            if cval.cidx = cval'.cidx then
              sameCtor {
                inductInfo := ival
                ctorInfo := cval
                leftFields := fields
                rightFields := fields'
                leftCtorApp := ctorApp
                rightCtorApp := ctorApp'
                val
              }
            else
              differentCtor {
                inductInfo := ival
                leftCtor := cval
                rightCtor := cval'
                leftFields := fields
                rightFields := fields'
                leftCtorApp := ctorApp
                rightCtorApp := ctorApp'
                val
              }

/--
Creates a helper that matches on the first two arguments, calling `sameCtor` for alternatives where
both sides use the same constructor, and `differentCtor` once for a fallback alternative where both
sides have provably different constructor indices.

The additional `α` argument receives the result of the `preHelpers` computation provided to
`makeInstancesUsingMutualBlock`. If you don't use `preHelpers`, you can simply ignore this
parameter.

Often, the right thing to do for the `sameCtor` branch is to use `foldSimilarVarsParallel` on the
`leftFields` and `rightFields` of the `SameCtorAlt`.

For a slower variant that however allows you to handle every constructor pair separately,
use `FieldHelperProvider.doubleCasesSlow`.
-/
def FieldHelperProvider.doubleCases
    (differentCtor : DifferentCtorFallbackAlt α → DerivingM Expr)
    (sameCtor : SameCtorAlt α → DerivingM Expr) :
    FieldHelperProvider α := fun input =>
  return .usingHelper fun _ val => do
    let fail := throwError "Invalid use of `{.ofConstName decl_name%}`, \
      expected field `{.ofConstName input.fieldName}` to have the shape \
      `α → α → β` where `α` is the type parameter"
    let .forallE _ ty (.forallE _ ty' tgt _) _ := input.expectedType | fail
    unless ty == input.typeApp do return ← fail
    unless ty' == input.typeApp do return ← fail
    if tgt.hasFVar || tgt.hasLooseBVars then
      throwError "Invalid use of `{.ofConstName decl_name%}`, the target type for \
        `{.ofConstName input.fieldName}` depends on the type parameter or the field arguments"
    let inductInfo ← getConstInfoInduct input.induct
    withLocalDeclD `lhs input.typeApp fun lhs => do
    withLocalDeclD `rhs input.typeApp fun rhs => do
      let lhsCIdx ← mkCtorIdxApp lhs
      let fallbackBranch (cidxNeProof : Expr) := do
        let cidxNeProof := mkApp4 (.const ``Ne.symm [1])
          Nat.mkType (← mkCtorIdxApp rhs) lhsCIdx cidxNeProof
        differentCtor { inductInfo, lhs, rhs, cidxNeProof, val }
      let res ← matchCtorIdxEq rhs lhsCIdx tgt (fallbackBranch := fallbackBranch) fun hcidx => do
        -- it is not be a free variable if the inductive has <= 1 constructor
        -- in which case `hcidx == (rfl : 0 = 0)`
        let toRevert := if hcidx.isFVar then #[rhs, hcidx] else #[rhs]
        let tgt ← mkForallFVars toRevert tgt
        let res ← mkDepCases lhs tgt fun ival cval fields ctorApp tgt => do
          forallBoundedTelescope tgt toRevert.size fun newVars tgt => do
            let rhs := newVars[0]!
            let hcidx := newVars[1]?.getD hcidx
            let res ← mkNondepCtorElim rhs tgt cval.name hcidx fun _ival _cval fields' ctorApp' => do
              prependError m!"Error while processing constructor {.ofConstName cval.name}:" do
                sameCtor {
                  inductInfo := ival
                  ctorInfo := cval
                  leftFields := fields
                  rightFields := fields'
                  leftCtorApp := ctorApp
                  rightCtorApp := ctorApp'
                  val
                }
            mkLambdaFVars newVars res
        return mkAppN res toRevert
      mkLambdaFVars #[lhs, rhs] res

private def reduceCasesOnApps (e : Expr) : MetaM Expr := do
  Meta.transform (skipConstInApp := true) e fun e => do
    let .const c _ := e.getAppFn | return .continue
    let .str ind sfx := c | return .continue
    unless sfx == casesOnSuffix do return .continue
    let some inductInfo ← isInductive? ind | return .continue
    let majorPos := inductInfo.numParams + 1 /- motive -/ + inductInfo.numIndices
    let paramCount := majorPos + 1 /- major -/ + inductInfo.numCtors
    let numArgs := e.getAppNumArgs
    if numArgs < paramCount then
      return .continue
    let major := e.getArg! majorPos numArgs
    let .const c' _ := major.getAppFn | return .continue
    let some ctorInfo ← isCtor? c' | return .continue
    unless ctorInfo.induct == ind do return .continue -- ill-typed or something
    let ctorFields := major.getAppArgsN ctorInfo.numFields
    let overArgs := e.getAppArgsN (numArgs - paramCount)
    return .visit <| e.getArg! (majorPos + 1 + ctorInfo.cidx) |>.beta (ctorFields ++ overArgs)

/--
Creates a helper that matches on the first argument, calling `perCtor` for each constructor with
the inductive info, constructor info, fields, constructor application and expected type with
`casesOn` applications reduced.

This is meant for laws about fields generated by `FieldHelperProvider.cases`.
-/
def FieldHelperProvider.casesLaw
    (perCtor : InductiveVal → ConstructorVal → Array Expr → Expr → Expr → α → DerivingM Expr) :
    FieldHelperProvider α := fun input =>
  return .usingHelper fun _ val => do
    let .forallE _ t tgt _ := input.expectedType
      | throwError "Invalid use of `{.ofConstName decl_name%}`, \
          expected field `{.ofConstName input.fieldName}` to have the shape \
          `α → β` where `α` is the type parameter"
    if t != input.typeApp then
      throwError "Invalid use of `{.ofConstName decl_name%}`, the argument to \
        `{.ofConstName input.fieldName}` is not the type parameter"
    withLocalDeclD `t input.typeApp fun discr => do
      let tgt := tgt.instantiate1 discr
      mkLambdaFVars #[discr] <| ← mkDepCases discr tgt fun ival cval fields ctorApp tgt => do
        -- This induces a total cost of O(n^2). If this becomes a problem we can consider using a
        -- different approach here
        let tgt ← reduceCasesOnApps tgt
        prependError m!"Error while processing constructor {.ofConstName cval.name}:" do
          perCtor ival cval fields ctorApp tgt val

private def reduceInstanceProjsOnCtor (e : Expr) : MetaM Expr := do
  Meta.transform (skipConstInApp := true) e fun e => do
    let .const projFn _ := e.getAppFn | return .continue
    let some info ← getProjectionFnInfo? projFn | return .continue
    unless info.fromClass do return .continue
    if e.getAppNumArgs ≤ info.numParams then return .continue
    let numOverargs := e.getAppNumArgs - info.numParams - 1
    let major := e.getArg! info.numParams
    let .const c _ := major.getAppFn | return .continue
    unless c == info.ctorName do return .continue
    let argIdx := info.numParams + info.i
    if major.getAppNumArgs ≤ argIdx then return .continue
    return .visit <| mkAppN (major.getArg! argIdx) (e.getAppArgsN numOverargs)

/--
Post-process function for `InstanceInfo.usingCtor`: reduces instance projections on constructors
in the value and removes the `partial` modifier if `usePartial` is false.
-/
def postprocessUsingCtor (usePartial : Bool) (predef : PreDefinition) : MetaM PreDefinition := do
  let value ← reduceInstanceProjsOnCtor predef.value
  return {
    predef with
    value
    modifiers.recKind := if usePartial then .partial else .default
  }

/--
Computes a type class application based on a type application.

First checks that the type former has one type parameter and then tries to synthesize all instance
parameters, instantiating them with the type application and setting level parameters appropriately.
-/
private def computeClassApp (typeApp : Expr) : DerivingM Expr := do
  let className := (← read).className
  let val ← getConstVal className
  let levelParams := val.levelParams
  unless levelParams.length ≤ 1 do
    throwError "Invalid use of `{.ofConstName decl_name%}`, expected \
      `{.ofConstName className}` to have at most one level parameter"
  let .forallE _ (.sort univ) _ _ := val.type
    | throwError "Invalid use of `{.ofConstName decl_name%}`, \
        expected `{.ofConstName className}`'s first parameter to be a type parameter"
  let mut classLParams := []
  if let [u] := levelParams then
    if univ == .param u then
      classLParams := [(← read).indLevel]
    else if univ == .succ (.param u) then
      classLParams := [← decLevel (← read).indLevel]
    else
      throwError "Invalid use of `{.ofConstName decl_name%}`, expected type parameter \
        to be either fully universe polymorphic or `Type u`-polymorphic"
  else
    classLParams := []
    unless univ.isEquiv (← read).indLevel do
      throwError "Invalid use of `{.ofConstName decl_name%}`, incorrect level for inductive"
  let mut res : Expr := .app (.const className classLParams) typeApp
  let mut more ← inferType res
  repeat
    more ← whnf more
    if more.isSort then
      break
    let .forallE _ t body bi := more
      | throwError "Invalid use of `{.ofConstName decl_name%}`, unexpected result type \
        for inductive:{indentExpr more}"
    unless bi.isInstImplicit do
      throwError "Invalid use of `{.ofConstName decl_name%}`, expected type class to only have \
        instance implicit parameters except for the type parameter"
    let cres ← tryApplyCanonicalInstance t
    match cres with
    | .ok (val, subgoals) =>
      let mut allLInsts := (← getLocalInstances) ++ (← get).newLInsts
      for (subgoal, allow) in subgoals do
        let (val, newAllLInsts) ← synthInstanceDerivingAux (← subgoal.getType) allLInsts allow
        subgoal.assign val
        allLInsts := newAllLInsts
      let val ← instantiateMVars val
      more := body.instantiate1 val
      res := res.app val
    | .error err =>
      let mut note : MessageData := ""
      let requiredClass ← withReducible <| forallTelescopeReducing (whnfType := true) t fun _ body =>
        pure (body.getAppFn.constName?.getD `missing)
      unless (← read).names.contains typeApp.getAppFn.constName! do
        let mut howToDerive := m!""
        if ← hasDerivingHandler requiredClass then
          howToDerive := m!"You can add a `deriving {.ofConstName requiredClass}` clause to all \
            inductives in the mutual group or use\
            {indentD m!"deriving instance {.ofConstName requiredClass} for \
              {.joinSep ((← read).indInfo.all.map MessageData.ofConstName) ", "}"}\
            \nto derive the missing instances"
        note := .note m!"This deriving handler operates on the entire mutual block, so even if \
          you don't need an instance for `{.ofConst typeApp.getAppFn}`, all of its instance \
          binders will still need to be synthesizeable.{howToDerive}"
      throwError "Failed to derive `{.ofConstName className}` for `{.ofConst typeApp.getAppFn}`: \
        Could not find a suitable instance for the instance parameter of type{indentExpr t}\
        \nReason:{indentD (← err.toMessageData)}{note}"
  return res

private def recurrenceError (inducts : List Name) (complexOnly : Bool)
    (msg : Name → Nat → Expr → String → MessageData) :
    MetaM (Option MessageData) := do
  for ind in inducts do
    let indInfo ← getConstInfoInduct ind
    for ctor in indInfo.ctors do
      forallTelescope (← getConstInfoCtor ctor).type fun vars _ => do←
        let fields := vars.drop indInfo.numParams
        for h : i in 0...fields.size do
          let fieldType ← inferType fields[i]
          if fieldType.find? (fun | .const c _ => c ∈ inducts | _ => false) |>.isSome then
            let res ← whnfD fieldType
            let .const c _ := res.getAppFn
              | return msg ctor i fieldType (if res.isForall then "reflexive" else "nested")
            unless c ∈ inducts do return msg ctor i fieldType "nested"
            unless complexOnly do
              return msg ctor i fieldType "normal"
  return none

/--
General version of `InstanceInfo.usingCtor` that allows specifying the precise type and type class
applications and variables to be abstracted (usually the indices).
-/
def InstanceInfo.usingCtorCore (perField : Name → FieldHelperProvider α)
    (induct : Name) (typeApp classApp : Expr) (additionalVars : Array Expr)
    (supportsRec : Bool := true) (supportsPartial := true)
    : DerivingM (InstanceInfo α) := do
  let usePartial := ((← isNestedOrReflexive) || !supportsRec)
    -- if we support partial but not recursion with termination
    -- we may as well use it for non-recursive inductives to be safe
    && ((← isRecursive) || supportsPartial)
  if usePartial && !supportsPartial then
    let indInfo := (← read).indInfo
    let className := (← read).className
    throwError .ofLazyM do
      let failureKind := if supportsRec then "nested and reflexive" else "recursive"
      let header := m!"Failed to derive `{.ofConstName className}`, this deriving handler does \
          not work for {failureKind} inductives"
      let where? ← recurrenceError indInfo.all supportsRec fun ctorName fieldIdx type kind =>
        m!" but the field #{fieldIdx + 1} of {.ofConstName ctorName} \
          contains a {kind} recurrence:{indentExpr type}"
      return m!"{header}{where?.getD "."}"
  let classApp ← whnfR classApp -- unfold class `abbrev`s like `Std.ReflOrd`
  classApp.withApp fun fn classParams => do
  let .const className classLParams := fn
    | throwError "Invalid use of `{.ofConstName decl_name%}`,{indentExpr classApp}\
        \nis not a constant application"
  let some structInfo := getStructureInfo? (← getEnv) className
    | throwError "Invalid use of `{.ofConstName decl_name%}`, \
        expected `{.ofConstName className}` to be a structure"
  let classInfo ← getConstInfoInduct className
  let [ctor] := classInfo.ctors | unreachable!
  let type ← mkForallFVars additionalVars classApp
  let mut fieldHelperInfos : Array (FieldHelperInfo α) := {}
  let mut helpers : Array (HelperInfo α) := #[]
  let additionalVarDecls := (← additionalVars.mapM (·.fvarId!.getDecl)).toList
  for h : i in 0...structInfo.fieldNames.size do
    let some projFn := structInfo.getProjFn? i | unreachable!
    let fieldInfo ← getConstVal projFn
    let expectedType ← Core.instantiateTypeLevelParams fieldInfo classLParams
    let expectedType ← instantiateForall expectedType classParams
    let .forallE _ _ expectedType _ := expectedType | unreachable!
    if expectedType.hasLooseBVars then
      throwError "Invalid use of `{.ofConstName decl_name%}`: This function can currently only \
        be used for non-dependent fields but `{.ofConstName projFn}` \
        depends on previous fields."
    let input := { classLParams, classParams, typeApp, fieldInfo, expectedType }
    let fieldHelperInfo ← perField projFn input
    fieldHelperInfos := fieldHelperInfos.push fieldHelperInfo
    if let .usingHelper mkValue := fieldHelperInfo then
      helpers := helpers.push {
        suffix := structInfo.fieldNames[i]
        type := ← mkForallFVars additionalVars expectedType
        mkValue instances val := do
          withExistingLocalDecls additionalVarDecls do
            let res ← mkLambdaFVars additionalVars <| ← mkValue instances val
            return res
        postprocess _ := postprocessUsingCtor usePartial
      }
  return {
    induct, type, helpers
    mkValue helpers := do
      withExistingLocalDecls additionalVarDecls do
        let mut ctorApp : Expr := mkAppN (.const ctor classLParams) classParams
        let mut helperIdx := 0
        for info in fieldHelperInfos do
          match info with
          | .inline e => ctorApp := ctorApp.app e
          | .usingHelper _ =>
            ctorApp := ctorApp.app (mkAppN helpers[helperIdx]! additionalVars)
            helperIdx := helperIdx + 1
        mkLambdaFVars additionalVars ctorApp
  }

/--
The building block for `makeInstancesUsingCtor`: `InstanceInfo.usingCtor` creates an `InstanceInfo`
for use in `makeInstancesUsingMutualBlock` that constructs an instance of the class using its
constructor and runs `perField` on every field given the name of the projection function of the
field.

See `makeInstancesUsingCtor` for an explanation of the arguments.

In most cases, the convenience function `makeInstancesUsingCtor` should be preferred over this one.
-/
def InstanceInfo.usingCtor (perField : Name → FieldHelperProvider α)
    (supportsRec : Bool := true) (supportsPartial := true)
    (induct : Name) : DerivingM (InstanceInfo α) := do
  let typeApp ← inductAppWithParams induct
  let indInfo ← getConstInfoInduct induct
  forallBoundedTelescope (← inferType typeApp) indInfo.numIndices fun indices body => do
    let .sort _ := body
      | throwError "Unexpected inductive type type{indentExpr (← inferType typeApp)}"
    let typeApp := mkAppN typeApp indices
    let classApp ← computeClassApp typeApp
    InstanceInfo.usingCtorCore perField induct typeApp classApp indices supportsRec supportsPartial

/--
Constructs instances of the type class in the context using its constructor, running `perField` on
every field given the name of the projection function of the field.

If `supportsRec := true` (the default), it tries to make the helpers non-partial if the inductive
is not nested or reflexive. If the helpers are possibly recursive but don't have structural
termination, you should consider using `supportsRec := false`.

If `supportsPartial := false`, the deriving handler will fail if the circumstances would cause it
to be partial (i.e. if the inductive is nested or reflexive or `supportsRec := false`). For data
type deriving handlers, `partial` is usually fine because of the existence of a `Nonempty` or
`Inhabited` instance for the result. However, for e.g. law type classes, the helpers will usually
not work with `partial`. Instead of providing an obscure error message about a missing `Nonempty`
instance, `supportsPartial := false` causes it to fail early with a more helpful error message.

If `nonRec := true`, then an instance is derived for each inductive individually. That means that
you can't refer to instances of other inductives in the mutual block. Use this for instances that
don't need recursive instance applications for the fields.

You can also specify a one-time computation at `preHelpers` which will be run before any of the
helpers with all helpers in scope. The result of this computation is provided as an additional `α`
argument to all `FieldHelperProvider` APIs.

Example:
```
open Lean Meta Elab Deriving

class TypeInfo (α : Type u) where
  nestedTypes : α → (acc : NameSet := {}) → NameSet
  inductName : Name

meta def deriveTypeInfo : DerivingHandler :=
  mkInductiveDerivingHandler ``TypeInfo do
    makeInstancesUsingCtor fun
      | ``TypeInfo.nestedTypes =>
        -- using the `FieldHelperProvider.cases` helper
        .cases fun inductVal _ctorVal fields _ctorApp _ => do
          withLocalDeclD `set (mkConst ``NameSet) fun accVar => do
            let mut acc := accVar
            acc := mkApp2 (.const ``NameSet.insert []) acc (toExpr inductVal.name)
            for field in fields do
              let type ← inferType field
              -- Proofs live in `Prop`, not in `Type u`, so we skip them.
              let some u ← getDecLevel? type | continue
              let inst ← synthInstanceDeriving (.app (.const ``TypeInfo [u]) type)
              let nm := mkApp2 (.const ``TypeInfo.inductName [u]) type inst
              acc := mkApp2 (.const ``NameSet.insert []) acc nm
              acc := mkApp4 (.const ``TypeInfo.nestedTypes [u]) type inst field acc
            mkLambdaFVars #[accVar] acc
      | ``TypeInfo.inductName =>
        -- or directly using the definition of `FieldHelperProvider`
        fun input => return .inline <| toExpr input.induct
      -- throws an error if we add a new field to `TypeInfo`
      -- without adding a new branch here
      | _ => .unhandled
    return true

meta initialize registerDerivingHandler ``TypeInfo deriveTypeInfo
```

This function is a short-hand for running `makeInstancesUsingMutualBlock` where each `InstanceInfo`
is generated using `InstanceInfo.usingCtor`.
-/
def makeInstancesUsingCtor (perField : Name → FieldHelperProvider α)
    (supportsRec : Bool := true) (supportsPartial := true) (nonRec : Bool := false)
    (preHelpers : DerivingM α := by exact pure ()) :
    DerivingM Unit := do
  if nonRec then
    for name in (← read).names do
      withoutModifyingInstanceState do
        makeInstancesUsingMutualBlock (preHelpers := preHelpers) <|
          #[← InstanceInfo.usingCtor perField supportsRec supportsPartial name]
  else
    makeInstancesUsingMutualBlock (preHelpers := preHelpers) <|
      ← (← read).indInfo.all.toArray.mapM
        (InstanceInfo.usingCtor perField supportsRec supportsPartial)

/-- An equation for an instance projection of an instance parameter of a law type class -/
structure InstanceProjEquation where
  /-- The class projection this equation applies to -/
  projName : Name
  /-- The projection info for `projName` -/
  projInfo : ProjectionFunctionInfo
  /-- The instance this equation applies to -/
  inst : Expr
  /-- The projection `inst.projName` -/
  lhs : Expr
  /-- The unfolded value, potentially recursive -/
  unfolded : Expr
  /-- A proof of `lhs = unfolded` -/
  proof : Expr
  /--
  The name of the helper declaration containing the unfolded value or `none` if the unfolded value
  came directly from the instance. If this is `none`, the value is guaranteed to be non-recursive.
  -/
  helperName? : Option Name

instance : ToMessageData InstanceProjEquation where
  toMessageData eqn := m!"{eqn.lhs}\n===>\n{eqn.unfolded}"

/-- Context for deriving law type classes -/
structure LawDerivingContext where
  /--
  Equations for instance projections of instance parameters of the law type class, keyed by
  projection name. In most cases, there is just one equation per projection name but there can be
  multiple if the law type class takes in two different instance parameters for the same type
  class.
  -/
  equations : NameMap (Array InstanceProjEquation) := {}
deriving Inhabited

/--
Given an application, returns the corresponding equation if `app` is an application of an instance
projection that is registered in the given context and the number of additional arguments
(`0` if `app` is not an over-application of the projection).
-/
def LawDerivingContext.findEquationFor? (ctx : LawDerivingContext) (app : Expr) :
    MetaM (Option (InstanceProjEquation × Nat)) := do
  let .const c _ := app.getAppFn | return none
  let numArgs := app.getAppNumArgs
  let some eqns := ctx.equations.find? c | return none
  for eqn in eqns do
    let majorIdx := eqn.projInfo.numParams
    if majorIdx >= numArgs then
      return none
    let major := app.getArg! majorIdx numArgs
    if ← withImplicit <| isDefEq major eqn.inst then
      return some (eqn, numArgs - majorIdx - 1)
  return none

/--
Unfolds all instance projections registered in `ctx` once in the expression `e`, returning
`(e', proof)` where `proof : e = e'`. You can also provide a filter for which projections to
unfold.
-/
def LawDerivingContext.unfoldOnce (ctx : LawDerivingContext) (e : Expr)
    (filter : InstanceProjEquation → Bool := fun _ => true) : MetaM (Expr × Expr) := do
  let methods : Simp.Methods := {
    post e := do
      let some (eqn, numOverArgs) ← ctx.findEquationFor? e | return .done { expr := e }
      unless filter eqn do return .done { expr := e }
      let overArgs := e.getAppArgsN numOverArgs
      let mut proof := eqn.proof
      for arg in overArgs do
        if proof.isAppOfArity ``funext 5 then
          -- fast and most common path
          proof := proof.appArg!.betaRev #[arg]
          continue
        proof ← mkCongrFun proof arg
      let rhs := eqn.unfolded.beta overArgs
      return .done {
        expr := rhs
        proof? := mkExpectedPropHint proof (← mkEq e rhs)
      }
    dpre e := do
      -- stop early
      return .done e
  }
  let simpCtx ← Simp.mkContext Simp.neutralConfig {} (← getSimpCongrTheorems)
  let (res, _) ← Simp.simp e |>.run simpCtx (methods := methods)
  return (res.expr, ← res.getProof)

/--
Unfolds all instance projections registered in `ctx` once in the expected type before running `x`.
You can also provide a filter for which projections to unfold.
-/
partial def LawDerivingContext.withUnfoldOnce (ctx : LawDerivingContext)
    (x : FieldHelperProvider α) (filter : InstanceProjEquation → Bool := fun _ => true)
    : FieldHelperProvider α :=
  fun input => do
    -- returns (e', h : e' → e)
    -- we need to do this manually to make sure the general structure
    -- is preserved for termination proofs
    let rec goRewrite (e : Expr) : DerivingM (Expr × Expr) := withIncRecDepth do
      match e with
      | .forallE nm t b bi =>
        let noRewrite := do
          withLocalDecl nm bi t fun var => do
            let (b', imp) ← goRewrite (b.instantiate1 var)
            let e' ← mkForallFVars #[var] b'
            withLocalDeclD `h e' fun h => do
              return (e', ← mkLambdaFVars #[h, var] (imp.betaRev #[h.app var]))
        unless ← isProp t do
          return ← noRewrite
        let (t', proof) ← ctx.unfoldOnce t filter
        -- unfortunately, is does not seem to be possible to disable all reductions in `simp`
        -- in particular it will always instantiate metavariables and fold raw nat literals
        -- so this branch may not be hit even if we didn't unfold anything :(
        -- the `Sym.Simp` framework gives us more control but requires us to share all expressions
        if t' == t then
          return ← noRewrite
        let mp := mkApp3 (.const ``Eq.mp [0]) t t' proof
        let mpr := mkApp3 (.const ``Eq.mpr_prop []) t t' proof
        withLocalDecl nm bi t' fun var => do
          let (b', imp) ← goRewrite (b.instantiate1 (mpr.app var))
          let e' ← mkForallFVars #[var] b'
          withLocalDeclD `h e' fun h => do
          withLocalDecl nm bi t fun origVar => do

            return (e', ← mkLambdaFVars #[h, origVar]
              (imp.replaceFVar var (mp.app origVar) |>.betaRev #[h.app (mp.app origVar)]))
      | _ =>
        let (e', proof) ← ctx.unfoldOnce e filter
        return (e', mkApp3 (.const ``Eq.mpr [← getLevel e]) e e' proof)
    let (newExpectedType, imp) ← goRewrite input.expectedType
    let res ← x { input with expectedType := newExpectedType }
    match res with
    | .inline res =>
      if let .lam _ _ b _ := imp then
        return .inline <| b.instantiateBetaRevRange 0 1 #[res]
      else
        return .inline <| imp.app res
    | .usingHelper fn =>
      return .usingHelper <| fun xs val => do
        let res ← fn xs val
        if let .lam _ _ b _ := imp then
          return b.instantiateBetaRevRange 0 1 #[res]
        else
          return imp.app res

private structure Refold where
  lparams : List Level
  value : Expr

/-- Undoing the effect of `reduceInstanceProjsOnCtor` -/
private def applyRefolds (e : Expr) (table : NameMap Refold) : MetaM Expr := do
  let pre (e : Expr) := do
    let .const c _ := e.getAppFn | return .continue
    -- don't visit class constructors
    -- we don't want to turn `{ beq := instBEqXYZ.beq }` into `{ beq := (instBEqXYZ).beq }`
    if let some ctor ← isCtor? c then
      if isClass (← getEnv) ctor.induct then
        return .done e
    return .continue
  let post (e : Expr) := do
    let .const c us := e.getAppFn | return .done e
    if let some refold := table.find? c then
      if us.isEqv refold.lparams Level.isEquiv then
        return .done <| refold.value.betaRev e.getAppRevArgs
    return .done e
  Meta.transform (skipConstInApp := true) e (pre := pre) (post := post)

private structure LawDerivingAccumulator where
  refolds : NameMap Refold := {}
  unfolds : Array InstanceProjEquation := #[]

/-- Returns `(e', proof)` -/
private def getUnfoldEqnForExpr (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let .const helperName us := e.getAppFn | return none
  let some info ← isDefn? helperName | return none
  if let some eqn ← getUnfoldEqnFor? helperName (nonRec := false) then
    let mut eqnProof := .const eqn us
    let mut type ← inferType eqnProof
    let args := e.getAppArgs
    let eqnBinderCount := type.getForallArity
    eqnProof := mkAppN eqnProof (args.take eqnBinderCount)
    type ← instantiateForall type args
    if eqnBinderCount <= args.size then
      -- over-application (or just normal application)
      let some (_, _, rhs) := type.eq?
        | throwError "Unexpected equation type{indentExpr type}\nfor{indentExpr eqnProof}"
      let overArgs := args[eqnBinderCount...*]
      let mut rhs := rhs
      for arg in overArgs do
        eqnProof ← mkCongrFun eqnProof arg
        rhs := rhs.app arg
      return some (rhs, eqnProof)
    else
      -- under-application
      forallTelescope type fun vars body => do←
        let some (_, _, rhs) := body.eq?
          | throwError "Unexpected equation type{indentExpr type}\nfor{indentExpr eqnProof}"
        eqnProof := mkAppN eqnProof vars
        for var in vars.reverse do
          eqnProof ← mkFunExt (← mkLambdaFVars #[var] eqnProof)
        return some (← mkLambdaFVars vars rhs, eqnProof)
  -- non-recursive
  let value ← instantiateValueLevelParams (.defnInfo info) us
  return some (value.betaRev e.getAppRevArgs, ← mkEqRefl e)

private def findRefoldsAndEquationsIn (instApp : Expr) (acc : LawDerivingAccumulator) :
    DerivingM LawDerivingAccumulator := do
  withTraceNode `Elab.Deriving (fun _ => return m!"Processing instance {instApp}") do
  let .const instName us := instApp.getAppFn
    | trace[Elab.Deriving] "Not a constant application for instance parameter{indentExpr instApp}"
      return acc
  let some info ← isDefn? instName
    | trace[Elab.Deriving] "Failed to unfold instance parameter{indentExpr instApp}"
      return acc
  let value ← instantiateValueLevelParams (.defnInfo info) us
  lambdaTelescope value fun vars value => do
    value.withApp fun ctor ctorArgs => do
      matchConstCtor ctor (fun _ => pure acc) fun cval classLParams => do
        if cval.numParams + cval.numFields != ctorArgs.size then
          trace[Elab.Deriving] "Only found partial constructor application{indentExpr value}"
          return acc
        let instArgs := instApp.getAppArgs
        if instArgs.size != vars.size then
          trace[Elab.Deriving] "Instance parameter is a partial application{indentExpr instApp}"
          return acc
        let params := ctorArgs.take cval.numParams
        let some structInfo := getStructureInfo? (← getEnv) cval.induct | return acc
        let mut acc := acc
        let genInstApp := mkAppN (.const instName us) vars
        for idx in *...cval.numFields do
          let field := ctorArgs[cval.numParams + idx]!
          if ← isProof field then
            continue
          let projName := structInfo.getProjFn? idx |>.get!
          acc ← field.withApp fun helper helperArgs => do
            let instantiatedFieldValue := field.replaceFVars vars instArgs
            let projApp := mkAppN (.const projName classLParams) params |>.app genInstApp
            let realProj := projApp.replaceFVars vars instArgs
            let some projInfo ← getProjectionFnInfo? projName
              | throwError "Failed to find projection information for `{.ofConstName projName}`"
            let nonHelper := do
              let unfolded := instantiatedFieldValue
              let proof ← mkEqRefl realProj
              let newEqn := {
                projName, projInfo, unfolded, proof
                helperName? := none
                inst := instApp
                lhs := realProj
              }
              return { acc with unfolds := acc.unfolds.push newEqn }
            let .const helperName us := helper | nonHelper
            unless instName.eraseMacroScopes.isPrefixOf helperName.eraseMacroScopes do
              return ← nonHelper
            -- The helper takes the same arguments, in the same order
            -- This is true for the output of `InstanceInfo.usingCtor`
            unless helperArgs == vars do
              trace[Elab.Deriving] "Weird helper variables{indentExpr field}"
              return ← nonHelper
            let refold : Refold := { lparams := us, value := ← mkLambdaFVars helperArgs projApp }
            let acc := { acc with refolds := acc.refolds.insert helperName refold }
            let some (unfolded, proof) ← getUnfoldEqnForExpr instantiatedFieldValue
              | throwError "Could not unfold{indentExpr field}\
                \nThis usually means that the instance is either partial or non-exposed"
            let newEqn := {
              projName, projInfo, unfolded, proof
              helperName? := some helperName
              inst := instApp
              lhs := realProj
            }
            return { acc with unfolds := acc.unfolds.push newEqn }
        return acc

private def validateRefolds (acc : NameMap Refold) : DerivingM Unit := do
  let mut validated : NameSet := {}
  for (nm, _) in acc do
    if validated.contains nm then
      continue
    validated := validated.insert nm
    let some defnInfo ← isDefn? nm | continue
    for other in defnInfo.all do
      unless acc.contains other do
        throwError
          "Could not find helper declaration `{.ofConstName other}` inside an instance. \
            This usually means that the instances were derived individually instead of all in a \
            single `deriving instance` command. If you can, use `deriving ...` directly at the \
            declaration of `{.ofConstName (← read).indInfo.name}` instead of using \
            `deriving instance ... for ...`. Otherwise, join all `deriving instance ... for ...` \
            into a single one by specifying the instances in a comma-separated list"
      validated := validated.insert other

private def LawDerivingContext.ofRefoldsAndEquations
    (refolds : NameMap Refold) (eqns : Array InstanceProjEquation) :
    DerivingM LawDerivingContext := do
  let mut ctx : LawDerivingContext := {}
  for eqn in eqns do
    let proj := eqn.projName
    let rhs ← applyRefolds eqn.unfolded refolds
    trace[Elab.Deriving] "Refolded{indentExpr eqn.unfolded}\n===>{indentExpr rhs}"
    let eqn := { eqn with unfolded := rhs }
    ctx := {
      ctx with
      equations := ctx.equations.alter proj fun
        | none => some #[eqn]
        | some xs => some (xs.push eqn)
    }
  return ctx

private structure LawDerivingEntry where
  induct : Name
  lctx : LocalContext
  localInsts : LocalInstances
  typeApp : Expr
  classApp : Expr
  indices : Array Expr
  equations : Array InstanceProjEquation
  lawContext : LawDerivingContext := {}
deriving Inhabited

private def buildLawDerivingEntriesFor (names : List Name) :
    DerivingM (Array LawDerivingEntry) := do
  let mut refolds : NameMap Refold := {}
  let mut entries : Array LawDerivingEntry := #[]
  for induct in names do
    let indApp ← inductAppWithParams induct
    let indInfo ← getConstInfoInduct induct
    forallBoundedTelescope (whnfType := true) (← inferType indApp) indInfo.numIndices fun indices body => do←
      let .sort _ := body | throwError "Unexpected inductive type type{indentExpr (← inferType indApp)}"
      let typeApp := mkAppN indApp indices
      let classApp ← computeClassApp typeApp
      -- we're interested in the instance arguments (the first is a type argument)
      let instArgs := classApp.getAppArgs.drop 1
      let mut acc := { refolds, unfolds := #[] }
      for instArg in instArgs do
        acc ← findRefoldsAndEquationsIn instArg acc
      trace[Elab.Deriving] "{acc.unfolds}"
      entries := entries.push {
        induct, typeApp, classApp, indices
        equations := acc.unfolds
        lctx := ← getLCtx
        localInsts := ← getLocalInstances
      }
      refolds := acc.refolds
  validateRefolds refolds
  entries.mapM fun entry => do
    withLCtx entry.lctx entry.localInsts do
      return {
        entry with
        equations := #[]
        lawContext := ← LawDerivingContext.ofRefoldsAndEquations refolds entry.equations
      }

/--
Constructs instances of the law type class in the context using its constructor, running `perField`
on every field given a `LawDerivingContext` and the name of the projection function of the field.

The `LawDerivingContext` contains equations for each field of the instance parameters of the law
type class. The most typical use is to just `ctx.withUnfoldOnce` with it, unfolding the relevant
instance projections. Otherwise, you can also use `ctx.unfoldOnce` later on individual expressions
or directly look up equations.

If `supportsRec := false`, it will fail if the inductive is recursive. Otherwise it also always
fails if the inductive is nested or reflexive.

If `nonRec := true`, then an instance is derived for each inductive individually. That means that
you can't refer to instances of other inductives in the mutual block. Use this for instances that
don't need recursive instance applications for the fields.

You can also specify a one-time computation at `preHelpers` which will be run before any of the
helpers with all helpers in scope. The result of this computation is provided as an additional `α`
argument to all `FieldHelperProvider` APIs.

Example:
```
class Size (α : Type u) where
  size : α → Int

class LawfulSize (α : Type u) [Size α] where
  size_pos (x : α) : 0 < Size.size x

open Lean Meta Elab Deriving

-- Deriving handler for `Size` (see `deriveTransformationInstPerConstructor`)
meta def deriveSize : DerivingHandler :=
  mkInductiveDerivingHandler ``Size do
    deriveTransformationInstPerConstructor fun _ival _cval fields _ctorApp => do
      let mut size := toExpr (0 : Int)
      for field in fields do
        let ty ← inferType field
        let some lvl ← getDecLevel? ty | continue
        let inst ← synthInstanceDeriving (.app (.const ``Size [lvl]) ty)
        let val := mkApp3 (.const ``Size.size [lvl]) ty inst field
        if size == toExpr (0 : Int) then
          size := val
        else
          size := mkIntAdd size val
      let val := toExpr (1 : Int)
      if size == toExpr (0 : Int) then
        return val
      else
        return mkIntAdd size val

-- Deriving handler for `LawfulSize`
meta partial def deriveLawfulSize : DerivingHandler :=
  mkInductiveDerivingHandler ``LawfulSize do
    deriveLawClassUsingCtor fun
      | ctx, ``LawfulSize.size_pos =>
        -- unfold the `Size.size` instance projection in the expression `0 < Size.size x`
        ctx.withUnfoldOnce <|
          -- then, match on the `x : α` parameter and reduce the matcher created
          -- by `deriveTransformationInstPerConstructor`
          .casesLaw fun _ival _cval _fields _ctorApp expectedType () => do
            -- The goal should be `0 < body` at this point where `body` is the equation generated
            -- in the deriving handler above
            let_expr LT.lt _ _ _zero body := expectedType
              | throwError "Unexpected goal for `LawfulSize` deriving handler\
                  {indentExpr expectedType}"
            provePos body
      | _, _ => .unhandled
    return true
where
  -- We recursively prove positivity of the whole expression
  -- This prover can handle a little more than `deriveSize` produces
  -- That can allow it to handle some non-recursive hand-written instances, too
  provePos (e : Expr) : DerivingM Expr := do
    match_expr e with
    -- (l + r : Int)
    | HAdd.hAdd _ _ _ inst l r =>
      -- We cannot assume that the expression comes directly from the deriving handler
      -- So we need to perform all sorts of checks to make sure what we're doing is correct
      unless ← DefEq.isInstHAddInt inst do
        throwError "Unexpected addition instance{indentExpr inst}"
      return mkApp4 (.const ``Int.add_pos []) l r (← provePos l) (← provePos r)
    | c@Size.size α inst x =>
      -- Here's where we use `LawfulSize` instances recursively
      let lawInst ← synthInstanceDeriving (mkApp2 (.const ``LawfulSize c.constLevels!) α inst)
      return mkApp4 (.const ``LawfulSize.size_pos c.constLevels!) α inst lawInst x
    | _ =>
      -- We need to also handle the `1` literal (here, generally, any positive literal)
      if let some val ← getIntValue? e then
        if 0 < val then
          let p := mkIntLT (toExpr (0 : Int)) e
          let decidable := mkApp2 (.const ``Int.decLt []) (toExpr (0 : Int)) e
          return mkApp3 (.const ``of_decide_eq_true []) p decidable reflBoolTrue
        throwError "Value is not positive:{indentExpr e}"
      throwError "Unexpected goal for `LawfulSize` deriving handler: \
        Could not prove that{indentExpr e}\nis positive"

meta initialize
  registerDerivingHandler ``Size deriveSize
  registerDerivingHandler ``LawfulSize deriveLawfulSize
```
-/
def deriveLawClassUsingCtor
    (perField : LawDerivingContext → Name → FieldHelperProvider α)
    (supportsRec : Bool := true) (nonRec : Bool := false)
    (preHelpers : DerivingM α := by exact pure ()) :
    DerivingM Unit := do
  if nonRec then
    for name in (← read).names do
      withoutModifyingInstanceState do
        let entries ← buildLawDerivingEntriesFor [name]
        let entry := entries[0]!
        let info ← withLCtx entry.lctx entry.localInsts do
          InstanceInfo.usingCtorCore (perField entry.lawContext) entry.typeApp entry.classApp
            entry.indices (supportsRec := supportsRec) (supportsPartial := false) (induct := name)
        makeInstancesUsingMutualBlock (preHelpers := preHelpers) #[info]
  else
    let entries ← buildLawDerivingEntriesFor (← read).indInfo.all
    makeInstancesUsingMutualBlock (preHelpers := preHelpers) <|
      ← entries.mapM fun entry => do
        withLCtx entry.lctx entry.localInsts do
          InstanceInfo.usingCtorCore (perField entry.lawContext) entry.typeApp entry.classApp
            entry.indices (supportsRec := supportsRec) (supportsPartial := false)
            (induct := entry.induct)

/--
Derive an instance for a transformation type class by applying `perCtor` for each constructor
with the inductive info, constructor info, the fields, and the constructor application. A
transformation type class is a type class of the shape
```
class ClassName (α : Sort u) where -- or (α : Type u) or (α : Type)
  fieldName : α → TargetType
```

If `supportsRec := true` (the default), it tries to make the helpers non-partial if the inductive
is not nested or reflexive. If the helpers are possibly recursive but don't have structural
termination, you should consider using `supportsRec := false`.

If `nonRec := true`, then an instance is derived for each inductive individually. That means that
you can't refer to instances of other inductives in the mutual block. Use this for instances that
don't need recursive instance applications for the fields.

Example:
```
inductive SExpr where
  | atom (s : String)
  | list (xs : List SExpr)
deriving Inhabited

class ToSExpr (α : Type u) where
  toSExpr : α → SExpr

open Lean Meta Elab Deriving

meta def toSExprHandler : DerivingHandler :=
  mkInductiveDerivingHandler ``ToSExpr do
    deriveTransformationInstPerConstructor fun _indVal ctorVal fields _ctorApp => do
      let tag : Expr := .app (mkConst ``SExpr.atom) (toExpr ctorVal.name.getString!)
      let mut args := #[]
      for field in fields do
        let ty ← inferType field
        -- Proofs live in `Prop`, not in `Type u`, so we just provide a hole for them.
        let some u ← getDecLevel? ty
          | args := args.push (.app (mkConst ``SExpr.atom) (toExpr "_"))
            continue
        let inst ← synthInstanceDeriving (mkApp (.const ``ToSExpr [u]) ty)
        args := args.push (mkApp3 (.const ``ToSExpr.toSExpr [u]) ty inst field)
      if args.isEmpty then
        return tag
      return mkApp (mkConst ``SExpr.list) (← mkListLit (mkConst ``SExpr) (tag :: args.toList))

meta initialize registerDerivingHandler ``ToSExpr toSExprHandler
```
-/
def deriveTransformationInstPerConstructor
    (perCtor : InductiveVal → ConstructorVal → Array Expr → Expr → DerivingM Expr)
    (supportsRec : Bool := true) (nonRec : Bool := false) :
    DerivingM Bool := do
  -- this is supposed to be present, but if not, we let `InstanceInfo.usingCtor` complain
  if let some info := getStructureInfo? (← getEnv) (← read).className then
    if info.fieldNames.size != 1 then
      throwError "Invalid use of `{.ofConstName decl_name%}`, expected \
        `{.ofConstName (← read).className}` to have exactly one field but it has \
        {info.fieldNames.size} fields"
  makeInstancesUsingCtor
      (supportsRec := supportsRec) (nonRec := nonRec)
      fun _ => .cases fun ival cval fields ctorApp _ => perCtor ival cval fields ctorApp
  return true

private def decLevels : Level → NameSet → NameSet
  | .zero, set => set -- we will report an error later
  | .succ _, set => set
  | .max l l', set => decLevels l' (decLevels l set)
  | .imax l l', set => decLevels l' (decLevels l set)
  | .param u, set => set.insert u
  | .mvar _, _ => unreachable!

/--
A shape of a level: Provides instantiations of level parameters such that the level matches a
certain shape. Typical shapes are `.sortU` for arbitrary levels, `.typeU` for `u + 1`,
`.prop` for the level `0` and `.type` for `1`.
-/
structure LevelShape where
  /--
  Given a normalized universe level `lvl`, try to provide assignments of the level parameters
  `levelParams` such that `lvl.instantiateParams levelParams (← createLParams lvl levelParams)`
  plausibly matches the level shape modulo level equivalence along with modified lists of level
  parameters that were not fixed to a certain value.

  The number of outputs should be limited by `limit`; `0` means "no limit".
  -/
  createLParams : (lvl : Level) → (levelParams : List Name) → (limit : Nat) → Array (List Level × List Name)
  /-- Returns true if the given level matches the shape (syntactically) -/
  matchesShape : Level → Bool
  /--
  Given an arbitrary level, return an equivalent level that matches the level shape or error
  (using `indName` for error reporting).
  -/
  ensureShape : Level → (indName : Name) → MetaM { l : Level // matchesShape l }

private inductive LevelConstraint where
  | zero
  | one
  | succ
deriving Ord, Repr, DecidableEq

/-- Run `cont` on every assignment of levels -/
private def matchLevelCore [Monad m] (k : LevelConstraint) (lvl : Level)
    (cur : NameMap LevelConstraint) (cont : NameMap LevelConstraint → m Unit) : m Unit := do
  match lvl, k with
  | .zero, .zero => cont cur
  | .zero, .one => pure ()
  | .zero, .succ => pure ()
  | .succ _, .zero => pure ()
  | .succ u, .one => matchLevelCore .zero u cur cont
  | .succ _, .succ => cont cur
  | .max u v, .zero => matchLevelCore .zero u cur fun cur => matchLevelCore .zero v cur cont
  | .max u v, .one =>
    matchLevelCore .one u cur (fun cur => matchLevelCore .one v cur cont *> matchLevelCore .zero v cur cont)
    matchLevelCore .zero u cur (fun cur => matchLevelCore .one v cur cont)
  | .max u v, .succ =>
    matchLevelCore .succ u cur (fun cur => matchLevelCore .succ v cur cont *> matchLevelCore .zero v cur cont)
    matchLevelCore .zero u cur (fun cur => matchLevelCore .succ v cur cont)
  | .imax _ v, .zero => matchLevelCore .zero v cur cont
  | .imax u v, .one =>
    matchLevelCore .one v cur (fun cur => matchLevelCore .one u cur cont *> matchLevelCore .zero u cur cont)
  | .imax u v, .succ =>
    matchLevelCore .succ v cur (fun cur => matchLevelCore .succ u cur cont *> matchLevelCore .zero u cur cont)
  | .param nm, k =>
    if let some k' := cur.find? nm then
      if k' = k then
        cont cur
      else
        pure ()
    else
      cont (cur.insert nm k)
  | .mvar _, _ => pure () -- should be unreachable

private def matchLevel (k : LevelConstraint) (lvl : Level) (levelParams : List Name) (limit : Nat)
    : Array (List Level × List Name) :=
  let cont (map) : EStateM Unit (Array (List Level × List Name)) Unit := do
    let lparams := levelParams.map fun nm =>
      match map.find? nm with
      | none => .param nm
      | some .zero => .zero
      | some .one => .one
      | some .succ => .succ (.param nm)
    let levelParams := levelParams.filter (fun nm => map.find? nm matches none | some .succ)
    let size : Nat ← modifyGet fun xs =>
      let xs := xs.push (lparams, levelParams)
      (xs.size, xs)
    if size = limit then
      throw ()
  let res := matchLevelCore k lvl {} cont |>.run #[]
  match res with
  | .ok _ s | .error _ s => s

/-- Match an arbitrary level -/
def LevelShape.sortU : LevelShape where
  createLParams _ levelParams _ := #[(levelParams.map Level.param, levelParams)]
  matchesShape _ := true
  ensureShape l _ := return ⟨l, rfl⟩

/-- Match the level shape `Type u` -/
def LevelShape.typeU : LevelShape where
  createLParams := matchLevel .succ
  matchesShape l := l matches .succ _
  ensureShape l indName := do
    let some l := l.dec |
      throwError "Inductive `{.ofConstName indName}` is a predicate, \
        expected a data-carrying inductive"
    return ⟨.succ l, rfl⟩

/-- Match the level `Type` -/
def LevelShape.type : LevelShape where
  createLParams := matchLevel .one
  matchesShape l := l matches .succ .zero
  ensureShape l indName := do
    if l.isAlwaysZero then
      throwError "Inductive `{.ofConstName indName}` is a predicate, \
        expected a data-carrying inductive"
    unless l.isEquiv (.succ .zero) do
      throwError "Inductive `{.ofConstName indName}` lives in a universe that's too high, \
        expected `Type`"
    return ⟨.succ .zero, rfl⟩

/-- Match the level `Prop` -/
def LevelShape.prop : LevelShape where
  createLParams := matchLevel .zero
  matchesShape l := l matches .zero
  ensureShape l indName := do
    unless l.isAlwaysZero do
      throwError "Inductive `{.ofConstName indName}` is a data-carrying inductive, \
        expected a predicate"
    return ⟨.zero, rfl⟩

/--
Infers the level shape, using one of `.prop`, `.type`, `.sortU` or `.typeU` depending on the type
of the first argument of `className`.
-/
def inferLevelShape (className : Name) : MetaM LevelShape := do
  let val ← getConstVal className
  let .forallE _ t _ _ := val.type |
    throwError "Internal error in deriving handler for `{.ofConstName className}`:\n\
      Could not figure out level shape, unexpected type class type{indentExpr val.type}"
  match t with
  | .sort .zero => return .prop
  | .sort .one => return .type
  | .sort (.param _) => return .sortU
  | .sort (.succ (.param _)) => return .typeU
  | _ => throwError "Internal error in deriving handler for `{.ofConstName className}`:\n\
      Could not figure out level shape, unexpected type class type{indentExpr val.type}"

/--
A deriving handler for `className` that groups the inductive type names provided to the deriving
handler by mutual block and runs `perMutualBlock` on each of them with appropriate `DerivingM`
context.

`levelShape` is used to determine the level parameters for the inductive. If this argument is
unspecified, it is inferred automatically, using `.sortU`, `.typeU`, `.prop`, or `.type` depending on
whether the first argument of `className` requires `Sort u`, `Type u`, `Prop` or `Type`,
respectively.
-/
def mkInductiveDerivingHandler (className : Name) (perMutualBlock : DerivingM Bool)
    (levelShape : Option LevelShape := none) : DerivingHandler := fun names => do
  unless ← names.allM isInductive do
    return false
  -- We group by mutual block while keeping the order the user provided
  let mut blocks : Array (Array Name) := {}
  let mut idxOfBlock : NameMap Nat := {}
  let mut seen : NameSet := {}
  for name in names do
    if seen.contains name then
      throwError "Duplicate name `{.ofConstName name}` for deriving"
    seen := seen.insert name
    let info ← getConstInfoInduct name
    let headInd := info.all.head!
    if let some i := idxOfBlock.find? headInd then
      blocks := blocks.modify i (·.push name)
    else
      let i := blocks.size
      idxOfBlock := idxOfBlock.insert headInd i
      blocks := blocks.push #[name]
  let state ← get
  let inExposeSection := (← getScope).attrs.any (· matches `(Parser.Term.attrInstance| expose))
  for names in blocks do
    let fstInfo ← getConstInfoInduct names[0]!
    let nparams := fstInfo.numParams
    let mut hasPrivate := isPrivateName className
    for name in fstInfo.all do
      if isPrivateName name then
        hasPrivate := true
        continue
      let hasPrivateCtor := (← getConstInfoInduct name).ctors.any isPrivateName
      if inExposeSection && hasPrivateCtor then
        let mut note := m!""
        unless names.contains name do
          note := m!"(which is part of the same mutual block as `{.ofConstName fstInfo.name}`) "
        throwError "Cannot use `deriving ... @[expose]` with `{.ofConstName name}` {note}\
          as it has one or more private constructors"
      hasPrivate := hasPrivate || hasPrivateCtor
    let res ← liftTermElabM do
      let indLevel ← forallTelescopeReducing (whnfType := true) fstInfo.type fun _ body => do
        let .sort lvl := body | throwError "Unexpected inductive type type{indentExpr fstInfo.type}"
        pure lvl.normalize
      let levelShape ← levelShape.getDM (inferLevelShape className)
      let univPoly := deriving.univPoly.get (← getOptions)
      let univPolyLimit := deriving.univPoly.limit.get (← getOptions)
      let limit :=
        if univPoly then
          if univPolyLimit = 0 then
            0
          else
            univPolyLimit + 1
        else
          1
      let options := levelShape.createLParams indLevel fstInfo.levelParams limit
      if univPoly ∧ 0 < univPolyLimit ∧ univPolyLimit < options.size then
        let list := MessageData.joinSep
          (options.map fun (levels, _) => (Expr.const fstInfo.name levels).setPPUniverses true).toList
          "\n"
        throwError "Limit set by `deriving.univPoly.limit` exceeded: \
          Deriving an instance of `{.ofConstName className}` for `{.ofConstName fstInfo.name}` \
          would require more than {univPolyLimit} different instantiations of level parameters to \
          be exhaustive, including:{indentD list}\n\
          If you just want to generate one instance for the first option, use \
          `set_option deriving.univPoly false`. If you want to generate instances for all \
          instantiations, use `set_option deriving.univPoly.limit 0` \
          (note however that this may be quite expensive)."
      -- for error messages
      let options :=
        if options.isEmpty then
          #[(fstInfo.levelParams.map Level.param, fstInfo.levelParams)]
        else
          options
      for (lparams, newLevelParams) in options do
        let errorFn (msg : MessageData) : MessageData :=
          if options.size > 1 then
            m!"For the instantiation `{(Expr.const fstInfo.name lparams).setPPUniverses true}` \
              of level parameters (see option `deriving.univPoly`):{indentD msg}"
          else
            msg
        let res ← mapError (f := errorFn) do
          let mut indLevel' := indLevel.instantiateParams fstInfo.levelParams lparams
          indLevel' ← levelShape.ensureShape indLevel' fstInfo.name
          let indTypeType ← instantiateTypeLevelParams fstInfo.toConstantVal lparams
          forallBoundedTelescope indTypeType nparams fun params _ => do
            let ctx := {
              className
              levelParams := newLevelParams
              params := params
              paramLCtx := ← getLCtx
              paramLInsts := ← getLocalInstances
              indInfo := fstInfo
              indLParams := lparams
              indParams := params
              indLevel := indLevel'
              names := names
              isMeta := (← read).isMetaSection || names.all (isMarkedMeta (← getEnv))
            }
            withExporting (isExporting := inExposeSection && !hasPrivate) do
              perMutualBlock.run ctx
        unless res do
          return false
      return true
    unless res do
      -- backtrack
      set state
      return false
  return true

/--
For every name provided to the deriving handler, look for an instance of `derivedFrom (name ...)`
and pass both the instance application and its delta-reduced version to `perInstance`.

This function is currently limited to `derivedFrom` type classes that have the type as their only
parameter (and e.g. don't have additional instance assumptions).

You should prefer using `deriveLawClassUsingCtor` if the instances were derived using
`makeInstancesUsingCtor` or `deriveTransformationInstPerConstructor`.
-/
def deriveLawClassSimple (className derivedFrom : Name)
    (perInstance : (inst : Expr) → (instValue : Expr) → DerivingM Bool) :
    DerivingHandler := fun names => do
  let state ← get
  let res : Bool ← liftTermElabM do
    let instances ← getGlobalInstancesIndex
    for name in names do
      let some info ← isInductive? name | return false
      let arity := info.numParams + info.numIndices
      let instanceEntries := instances.getEntriesWithKeys
        (#[.const derivedFrom 1, .const name arity] ++ Array.replicate arity .star)
      let instanceEntries ← filterActiveInstances instanceEntries
      if instanceEntries.isEmpty then
        let hint := .hint' m!"Adding the command \
          `deriving instance {.ofConstName derivedFrom} for {.ofConstName name}` \
          may allow Lean to derive the missing instance."
        throwError "Failed to derive `{.ofConstName className}` for `{.ofConstName name}`; \
          it is a law type class for `{.ofConstName derivedFrom}` \
          but there is no `{.ofConstName derivedFrom}` instance for `{.ofConstName name}`.\
          {hint}"
      let some idx ← chooseInstance instanceEntries |
        throwError "There are multiple `{.ofConstName derivedFrom}` instances for \
          `{.ofConstName name}`, namely: {.andList (instanceEntries.map (·.val)).toList}"
      let instEntry := instanceEntries[idx]
      let some instName := instEntry.globalName? |
        throwError "Expected instance to have a global name:{indentExpr instEntry.val}"
      let .defnInfo instInfo ← getConstInfo instName |
        throwError "Instance `{.ofConstName instName}` does not have an exposed body"
      let levelParams := instInfo.levelParams
      let res ← forallTelescopeReducing (whnfType := true) instInfo.type fun vars res => do
        unless res.isAppOfArity derivedFrom 1 do
          throwError "Expected result type of instance {.ofConstName instName} to be the class \
            {.ofConstName derivedFrom} but found{indentExpr res}"
        let indApp := (← whnfR res.appArg!)
        indApp.withApp fun indFn indArgs => do
          unless indFn.isConstOf name do
            throwError "Expected argument of instance {MessageData.ofConstName instName} to be an \
              application of the type {MessageData.ofConstName name} but found:{indentExpr indApp}"
          let instApp := mkAppN (.const instInfo.name (instInfo.levelParams.map Level.param)) vars
          let instValue := instInfo.value.beta vars
          let ctx := {
            className, levelParams
            params := vars
            paramLCtx := ← getLCtx
            paramLInsts := ← getLocalInstances
            indInfo := info
            indLParams := indFn.constLevels!
            indParams := indArgs
            indLevel := ← getLevel indApp
            names := #[name]
            isMeta := false -- no compilation
          }
          withoutExporting do -- exposing doesn't make sense for proofs
            (perInstance instApp instValue).run ctx
      unless res do
        return false
    return true
  unless res do
    -- backtrack
    set state
  return res

/--
Derive instances for `@className (@name ...) ...` first using `preHandler` for all type names
provided to the deriving handler that don't yet have such an instance before running `handler`.
-/
def derivePrerequisite (className : Name) (preHandler : DerivingHandler)
    (handler : DerivingHandler) : DerivingHandler := fun names => do
  let prereqNames ← liftTermElabM do
    let instances ← getGlobalInstancesIndex
    let mut needToDerive := #[]
    for name in names do
      let typeFormer ← mkConstWithFreshMVarLevels name
      let (typeArgs, _, _) ← forallMetaTelescopeReducing (← inferType typeFormer)
      let typeApp := mkAppN typeFormer typeArgs
      let classApp ← mkConstWithFreshMVarLevels className
      let classApp := classApp.app typeApp
      let (classArgs, _, _) ← forallMetaTelescopeReducing (← inferType classApp)
      let classApp := mkAppN classApp classArgs
      let expectedPath ← DiscrTree.mkPath classApp
      let instanceEntries := instances.getEntriesWithKeys expectedPath
      let instanceEntries ← filterActiveInstances instanceEntries
      if instanceEntries.isEmpty then
        needToDerive := needToDerive.push name
    return needToDerive
  let state ← get
  unless ← preHandler prereqNames <&&> handler names do
    -- backtrack
    set state
    return false
  return true

end Lean.Meta.Deriving
