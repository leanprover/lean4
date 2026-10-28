/-
Copyright (c) 2026 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez
-/
module

prelude
public import Lean.Elab.PreDefinition
public import Lean.Elab.Deriving.Basic

public section

open Lean Meta Elab Command Term

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

inductive CanonicalInstanceFailure where
  | nonUnique (matching filtered : Array InstanceEntry)
  | unifyFailed (instEntry : InstanceEntry)
  | hasMVars (mctx : MetavarContext) (instEntry : InstanceEntry) (e : Expr) (isArg : Bool)
deriving Inhabited

def CanonicalInstanceFailure.isNoMatch : CanonicalInstanceFailure → Bool
  | .nonUnique _ filtered => filtered.isEmpty
  | _ => false

def CanonicalInstanceFailure.isMultiMatch : CanonicalInstanceFailure → Bool
  | .nonUnique _ filtered => filtered.size > 1
  | _ => false

def CanonicalInstanceFailure.toMessageData : CanonicalInstanceFailure → MetaM MessageData
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
Without `deriving.chooseArbitraryInstance`, returns `some possible[0]` if `possible` has exactly
one element and `none` if it has no elements or more than one. Otherwise, returns the last instance
with the highest priority or `none` if `possible` is empty.
-/
private def chooseInstance (possible : Array InstanceEntry) : CoreM (Option InstanceEntry) := do
  if possible.isEmpty then
    return none
  if let #[single] := possible then
    return single
  unless deriving.chooseArbitraryInstance.get (← getOptions) do
    return none
  let mut best := possible[0]!
  for h : i in 1...possible.size do
    let inst := possible[i]
    if best.priority ≤ inst.priority then
      best := inst
  return best

/--
Given an instance type `instType`, try to apply a canonical instance, producing new instance
hypotheses as synthetic opaque metavariables.

The result of this function is a pair of the instance application and the list of new instance
hypotheses together with an indication of whether to run this function again on the resulting
instance obligation. We use a heuristic here to (try to) make sure we don't run into an infinite
loop.

Canonical instances are currently defined as instances with exactly two special fragments in the
discrimination tree keys (forall and constants except `Eq` and instance projections because of
`DecidableEq` and e.g. `TransOrd`). Furthermore, we only try an instance if it is the only one with
"good keys" (unless `deriving.chooseArbitraryInstance` is true).
-/
private def tryApplyCanonicalInstance (instType : Expr) :
    MetaM (Except CanonicalInstanceFailure (Expr × Array (MVarId × Bool))) := do
  let lctx ← getLCtx
  let linsts ← getLocalInstances
  forallTelescopeReducing (whnfType := true) instType fun vars body => do
    -- try to apply instance
    let instances ← getGlobalInstancesIndex
    let matching ← instances.getUnify body
    let env ← getEnv
    let matching ← filterActiveInstances matching
    let filtered := matching.filter fun inst => goodKeys inst.keys env
    let some instEntry ← chooseInstance filtered | return .error (.nonUnique matching filtered)
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
        outVars := outVars.push (arg.mvarId!, goodHypothesisKeys keys env)
    unless ← isDefEqI instBody body do
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
    -- If we have additional variables from `forallTelescopeReducing` here, we have to revert them
    unless vars.isEmpty do
      outVars ← outVars.mapM fun (outVar, allowMore) => do
        let mvarApp ← mkFreshRevertedMVarAt lctx linsts (← outVar.getType)
        outVar.assign mvarApp
        return (mvarApp.getAppFn.mvarId!, allowMore)
    trace[Elab.Deriving] "Result: {res}, {outVars}"
    return .ok (← mkLambdaFVars vars res, outVars)

structure State where
  instanceMVars : Array MVarId := #[]
  newLInsts : LocalInstances := #[]
  -- for documentation purposes
  invariant1 : instanceMVars.size = newLInsts.size := by rfl
  invariant2 (i : Nat) (hi : i < newLInsts.size) :
    newLInsts[i].fvar = .mvar instanceMVars[i] := by nofun
  splitFailures : Array (MVarId × CanonicalInstanceFailure) := #[]

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
  `mkAppN (mkAppN (.const indInfo.name lparams) indParams) indIndices : Sort indLevel`
  for any valid `indIndices`. In the case of `mkInductiveDerivingHandler`, this is guaranteed to
  match the level shape provided to the function (or inferred by `inferLevelShape`).
  -/
  indLevel : Level
  /--
  The names of the declarations within `indInfo.all` that we should generate instances for.
  -/
  names : Array Name
  /--
  Whether the generated instances should be `meta`.
  -/
  isMeta : Bool

abbrev DerivingM := ReaderT Deriving.Context <| StateRefT Deriving.State TermElabM

instance : Inhabited (DerivingM α) where
  default := liftM (default : TermElabM α)

nonrec def DerivingM.run (x : DerivingM α) (ctx : Deriving.Context) : TermElabM α :=
  (x.run ctx).run' {}

private def pushInstanceHypothesis (type : Expr) (className : Name) : DerivingM Expr := do
  -- We simply add the new metavariables as local instances for instance synthesis to pick up
  -- That way we can detect redundant instances more easily
  let mvarApp ← mkFreshRevertedMVarAt (← read).paramLCtx (← read).paramLInsts type
  let goal := mvarApp.getAppFn.mvarId!
  modify fun state => {
    state with
    instanceMVars := state.instanceMVars.push goal
    newLInsts := state.newLInsts.push { className, fvar := .mvar goal }
    invariant1 := by simpa using state.invariant1
    invariant2 i hi := by
      have := state.invariant1
      rw [Array.size_push] at hi
      rcases Nat.lt_add_one_iff_lt_or_eq.mp hi with hlt | rfl
      · rw [Array.getElem_push_lt hlt, state.invariant2 i hlt, Array.getElem_push_lt (by omega)]
      · rw [Array.getElem_push_eq, Array.getElem_push, dite_eq_right (by omega)]
  }
  return mvarApp

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
  for inst in allLInsts do
    if inst.className == className then
      if ← isDefEqI (← inferType inst.fvar) type then
        return inst.fvar
  return none

private partial def synthInstanceDerivingAux (type : Expr) (allLInsts : LocalInstances)
    (allowCanonicalInstanceReduction : Bool := true) : DerivingM Expr := withIncRecDepth do
  let some className ← isClass? type |
    throwError "type class instance expected{indentExpr type}"
  if let some res ← trySynthesize type allLInsts then
    return res
  let mut shouldTry := allowCanonicalInstanceReduction -- avoid loops
  if !deriving.reduceInstances.get (← getOptions) ||
      deriving.bindersVerbatim.get (← getOptions) then
    shouldTry := false
  unless shouldTry do
    -- if the instance requirement is nested (i.e. contains recursive occurrences),
    -- we *have* to reduce it, otherwise we end up with a useless instance like
    -- `instance [BEq (List Thing)] : BEq Thing`
    unless ← containsRecursiveDecl type do
      return ← pushInstanceHypothesis type className
    -- also, try instance synthesis even if it was disabled through `deriving.bindersVerbatim`
    if let .some res ← withLCtx (← getLCtx) allLInsts <| trySynthInstance type then
      return res
  let state ← (saveState : MetaM _)
  -- try reducing e.g. `BEq (List α)` to `BEq α`
  let res ← tryApplyCanonicalInstance type
  match res with
  | .ok (assignment, outVars) =>
    for (var, allow) in outVars do
      let res ← synthInstanceDerivingAux (← var.getType) allLInsts allow
      var.assign res
    instantiateMVars assignment
  | .error e =>
    if ← containsRecursiveDecl type then
      throwError "Got stuck at instance requirement for nested type while deriving an \
        instance for {.ofConstName (← read).className}:{indentExpr type}\n\
        Reason: {← e.toMessageData}"
    state.restore
    let res ← pushInstanceHypothesis type className
    let mvar := res.getAppFn.mvarId!
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
  instantiateMVars <| ← synthInstanceDerivingAux e allLInsts

private def blankLInst : LocalInstance where
  className := .anonymous
  fvar := .sort .zero

/--
Given a list of metavariables corresponding to instance obligations, eliminate redundant instances,
returning a suitable list of instance assumptions to be used in
`mkLambdaFVars (binderInfoForMVars := .instImplicit)`.

Precondition: The current local context must also be the local contexts of all metavariables.
-/
private def filterInstanceObligations (state : Deriving.State) : MetaM (Array MVarId) := do
  if deriving.bindersVerbatim.get (← getOptions) then
    return state.instanceMVars
  let n := state.instanceMVars.size
  let mut idxOfMVar : MVarIdMap (Fin n) := {}
  for h : i in 0...n do
    idxOfMVar := idxOfMVar.insert state.instanceMVars[i] ⟨i, h.2⟩
  -- j ∈ fwdDeps[i] ↔ j = i or j depends on i
  let mut fwdDeps : Array (Array (Fin n)) := Array.ofFn fun i : Fin n => #[i]
  for h : i in 0...n do
    let deps ← state.instanceMVars[i].getMVarDependencies
    for dep in deps do
      let some j := idxOfMVar.get? dep | continue
      fwdDeps := fwdDeps.modify j (·.push ⟨i, h.2⟩)
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
    for dep in fwdDeps[i]! do
      newLInsts := newLInsts.set (dep + m - n) blankLInst
    let mvar := state.instanceMVars[i]
    let mvarType ← mvar.getType
    if let .some res ← withLCtx lctx newLInsts.toArray (trySynthInstance mvarType) then
      -- add new dependencies
      mvar.assign res
      let deps ← res.getMVarDependencies
      for dep in deps do
        let some j := idxOfMVar.get? dep | continue
        fwdDeps := fwdDeps.modify j (·.push ⟨i, h⟩)
    -- restore the local instances
    for dep in fwdDeps[i]! do
      newLInsts := newLInsts.set (dep + m - n) oldLInsts[dep + m - n]
  let mut newMVars := #[]
  for mvar in state.instanceMVars do
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
Runs `x` with a new instance state: Instance binders created using `synthInstanceDeriving` within
`withNewInstanceState` don't persist into the outer scope and don't affect the result of
`produceInstanceHyps` in the outer scope; and any instance binders created before
`withNewInstanceState` don't persist into the inner scope and don't affect the result of
`produceInstanceHyps` in the inner scope.
-/
@[inline]
def withNewInstanceState (x : DerivingM α) : DerivingM α := do
  let oldState ← get
  set { : Deriving.State }
  try
    x
  finally
    set oldState

/--
Convenience function for creating an instance declaration with the given type and value and
instance hypotheses produced by `produceInstanceHyps`. The type and value may depend on any
parameters in the context as well as instances generated by `synthInstanceDeriving`.
-/
def mkInstanceForDeriving (instanceHyps : Array Expr) (type value : Expr)
    (name : Option Name := none) : DerivingM Unit := do
  let allVars := (← read).params ++ instanceHyps
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
(i.e. types with a `α → Induct ...` recurrence). In those cases, use `isNestedOrReflexive`.
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
Returns whether the recursors of the mutual inductive block being operated on only eliminate into proposition
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
  | { newNames }, env, nm => env.contains nm || newNames.contains nm

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
        let value ← helper.mkValue recInsts globalCompute
        return { helper with value := some <| value.replaceFVars recInsts instanceValues }
      return { info with extendedHelpers }
    let instHyps ← produceInstanceHyps
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
        return { helper with type, value }
      let value ← instantiateMVars info.value
      let value ← mkLambdaFVars allParams value (binderInfoForMVars := .instImplicit)
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
          kind := .def
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
    let nameSet : NameSet := .ofArray (← read).names
    for info in infos do
      unless nameSet.contains info.induct do continue
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
A field helper provider provides information on how a field of a type class should be filled given
level parameters for the class, an application of the inductive type to derive an instance for, a
`ConstantVal` for the instance projection function corresponding to the field and the expected type
of the field.
-/
@[expose]
def FieldHelperProvider (α : Type) :=
  (classLParams : List Level) → (typeApp : Expr) → (fieldInfo : ConstantVal) →
    (expectedType : Expr) → DerivingM (FieldHelperInfo α)

/--
Throws an error explaining that the given field was unhandled. Meant to be used as a catch-all
branch of `InstanceInfo.usingCtor`. See `InstanceInfo.usingCtor` for more information.
-/
def FieldHelperProvider.unhandled (fieldName : Name) : FieldHelperProvider α := fun _ _ _ _ => do
  throwError "Internal error in deriving handler for `{.ofConstName <| (← read).className}`:\n\
    Unhandled field `{.ofConstName fieldName}`"

/--
Creates a helper that matches on the first argument, calling `perCtor` for each constructor with
the inductive info, constructor info, fields and a constructor application.

The additional `α` argument receives the result of the `preHelpers` computation provided to
`makeInstancesUsingMutualBlock`. If you don't use `preHelpers`, you can simply ignore this
parameter.
-/
def FieldHelperProvider.cases
    (perCtor : InductiveVal → ConstructorVal → Array Expr → Expr → α → DerivingM Expr) :
    FieldHelperProvider α := fun _ typeApp fieldInfo expectedType =>
  return .usingHelper fun _ val => do
    let .forallE _ t tgt _ := expectedType
      | throwError "Invalid use of `{.ofConstName decl_name%}`, \
          expected field `{.ofConstName fieldInfo.name}` to have the shape \
          `α → β` where `α` is the type parameter"
    if t != typeApp then
      throwError "Invalid use of `{.ofConstName decl_name%}`, the argument to \
        `{.ofConstName fieldInfo.name}` is not the type parameter"
    withLocalDeclD `t typeApp fun discr => do
      let tgt := tgt.instantiate1 discr
      mkLambdaFVars #[discr] <| ← mkDepCases discr tgt fun ival cval fields ctorApp => do
        prependError m!"Error while processing constructor {.ofConstName cval.name}:" do
          perCtor ival cval fields ctorApp val

private def reduceInstanceProjsOnCtor (e : Expr) : MetaM Expr := do
  let env ← getEnv
  return e.replace fun e => do
    let .const projFn _ := e.getAppFn | failure
    let info ← env.getProjectionFnInfo? projFn
    unless info.fromClass do failure
    if e.getAppNumArgs ≤ info.numParams then failure
    let numOverargs := e.getAppNumArgs - info.numParams - 1
    let major := e.getArg! info.numParams
    let .const c _ := major.getAppFn | failure
    unless c == info.ctorName do failure
    let argIdx := info.numParams + info.i
    if major.getAppNumArgs ≤ argIdx then failure
    return mkAppN (major.getArg! argIdx) (e.getAppArgsN numOverargs)

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
Constructs an instance of the class using its constructor, running `perField` on every field given
the name of the projection function of the field.

For `supportsRec := true` (the default), it tries to make the helpers non-partial if the inductive
is not nested or reflexive. If the helpers are possibly recursive but don't have structural
termination, you should consider using `supportsRec := false`.

Example:
```
class TypeInfo (α : Type u) where
  ctorName : α → Name
  inductName : Name

open Lean Meta Elab Deriving

meta def deriveTypeInfo : DerivingHandler :=
  mkInductiveDerivingHandler ``TypeInfo do
    makeInstancesUsingMutualBlock <| ← (← read).indInfo.all.toArray.mapM <|
      InstanceInfo.usingCtor fun
        | ``TypeInfo.ctorName =>
          -- using the `FieldHelperProvider.cases` helper
          .cases fun _inductVal ctorVal _fields _ctorApp _ => do
            return toExpr ctorVal.name
        | ``TypeInfo.inductName =>
          -- or directly using the definition of `FieldHelperProvider`
          fun _classLParams typeApp _fieldInfo _expectedType =>
            return .inline <| toExpr typeApp.getAppFn.constName!
        -- throws an error if we add a new field to `TypeInfo`
        -- without adding a new branch here
        | name => .unhandled name
    return true

meta initialize registerDerivingHandler ``TypeInfo deriveTypeInfo
```
-/
def InstanceInfo.usingCtor (perField : Name → FieldHelperProvider α)
    (supportsRec : Bool := true) (induct : Name) :
    DerivingM (InstanceInfo α) := do
  let className := (← read).className
  let classInfo ← getConstInfoInduct className
  let levelParams := classInfo.levelParams
  unless classInfo.numParams = 1 ∧ levelParams.length ≤ 1 do
    throwError "Invalid use of `{.ofConstName decl_name%}`, expected \
      `{.ofConstName className}` to have exactly one parameter and at most one level parameter"
  let .forallE _ (.sort univ) _ _ ← whnf classInfo.type
    | throwError "Invalid use of `{.ofConstName decl_name%}`, \
        expected `{.ofConstName className}`'s parameter to be a type parameter"
  let some structInfo := getStructureInfo? (← getEnv) className
    | throwError "Invalid use of `{.ofConstName decl_name%}`, \
        expected `{.ofConstName className}` to be a structure"
  let [ctor] := classInfo.ctors | unreachable!
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
  let typeApp ← inductAppWithParams induct
  let indInfo ← getConstInfoInduct induct
  let usePartial := (← isNestedOrReflexive) || !supportsRec
  forallBoundedTelescope (whnfType := true) (← inferType typeApp) indInfo.numIndices fun indices body => do
    let .sort _ := body
      | throwError "Unexpected inductive type type{indentExpr (← inferType typeApp)}"
    let typeApp := mkAppN typeApp indices
    let type ← mkForallFVars indices <| .app (.const className classLParams) typeApp
    let mut fieldHelperInfos : Array (FieldHelperInfo α) := {}
    let mut helpers : Array (HelperInfo α) := #[]
    let indexDecls := (← indices.mapM (·.fvarId!.getDecl)).toList
    for h : i in 0...structInfo.fieldNames.size do
      let some projFn := structInfo.getProjFn? i | unreachable!
      let fieldCVal ← getConstVal projFn
      let expectedType ← Core.instantiateTypeLevelParams fieldCVal classLParams
      let expectedType ← instantiateForall expectedType #[typeApp]
      let .forallE _ _ expectedType _ := expectedType | unreachable!
      if expectedType.hasLooseBVars then
        throwError "Invalid use of `{.ofConstName decl_name%}`: This function can currently only \
          be used for non-dependent fields but `{.ofConstName projFn}` \
          depends on previous fields."
      let fieldHelperInfo ← perField projFn classLParams typeApp fieldCVal expectedType
      fieldHelperInfos := fieldHelperInfos.push fieldHelperInfo
      if let .usingHelper mkValue := fieldHelperInfo then
        helpers := helpers.push {
          suffix := structInfo.fieldNames[i]
          type := ← mkForallFVars indices expectedType
          mkValue instances val := do
            withExistingLocalDecls indexDecls do
              let res ← mkLambdaFVars indices <| ← mkValue instances val
              return res
          postprocess _ := postprocessUsingCtor usePartial
        }
    return {
      induct, type, helpers
      mkValue helpers := do
        withExistingLocalDecls indexDecls do
          let mut ctorApp : Expr := .app (.const ctor classLParams) typeApp
          let mut helperIdx := 0
          for info in fieldHelperInfos do
            match info with
            | .inline e => ctorApp := ctorApp.app e
            | .usingHelper _ =>
              ctorApp := ctorApp.app (mkAppN helpers[helperIdx]! indices)
              helperIdx := helperIdx + 1
          mkLambdaFVars indices ctorApp
    }

/--
Derive an instance for a transformation type class by applying `perCtor` for each constructor
with the inductive info, constructor info, the fields, and the constructor application. A
transformation type class is a type class of the shape
```
class ClassName (α : Sort u) where -- or (α : Type u) or (α : Type)
  fieldName : α → TargetType
```
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
        -- Proofs live in `Prop`, not in `Type u`, so we skip them.
        let some u ← getDecLevel? ty | continue
        let inst ← synthInstanceDeriving (mkApp (.const ``ToSExpr [u]) ty)
        args := args.push (mkApp3 (.const ``ToSExpr.toSExpr [u]) ty inst field)
      if args.isEmpty then
        return tag
      return mkApp (mkConst ``SExpr.list) (← mkListLit (mkConst ``SExpr) (tag :: args.toList))

meta initialize registerDerivingHandler ``ToSExpr toSExprHandler
```
For `supportsRec := true` (the default), it tries to make the helpers non-partial if the inductive
is not nested or reflexive. This however is only guaranteed to work if the fields provided to
`perCtor` are only used as arguments to the instance projection of the class
(i.e. `ToSExpr.toSExpr` in the example above). Otherwise, use `supportsRec := false`.
-/
def deriveTransformationInstPerConstructor
    (perCtor : InductiveVal → ConstructorVal → Array Expr → Expr → DerivingM Expr)
    (supportsRec : Bool := true) :
    DerivingM Bool := do
  -- this is supposed to be present, but if not, we let `InstanceInfo.usingCtor` complain
  if let some info := getStructureInfo? (← getEnv) (← read).className then
    if info.fieldNames.size != 1 then
      throwError "Invalid use of `{.ofConstName decl_name%}`, expected \
        `{.ofConstName (← read).className}` to have exactly one field but it has \
        {info.fieldNames.size} fields"
  makeInstancesUsingMutualBlock <| ← (← read).indInfo.all.toArray.mapM <|
    InstanceInfo.usingCtor (supportsRec := supportsRec)
      fun _ => .cases fun ival cval fields ctorApp _ => perCtor ival cval fields ctorApp
  return true

private def decLevels : Level → NameSet → NameSet
  | .zero, set => set -- we will report an error later
  | .succ _, set => set
  | .max l l', set => decLevels l' (decLevels l set)
  | .imax l l', set => decLevels l' (decLevels l set)
  | .param u, set => set.insert u
  | .mvar _, _ => unreachable!

structure LevelShape where
  /--
  Given a normalized universe level `lvl`, try to provide an assignment of the level parameters
  `levelParams` such that `lvl.instantiateParams levelParams (← createLParams lvl levelParams)`
  plausibly matches the level shape modulo level equivalence and return a modified list of level
  parameters that were not fixed to a certain value.
  -/
  createLParams : (lvl : Level) → (levelParams : List Name) → List Level × List Name
  /-- Returns true if the given level matches the shape (syntactically) -/
  matchesShape : Level → Bool
  /--
  Given an arbitrary level, return an equivalent level that matches the level shape or error
  (using `indName` for error reporting).
  -/
  ensureShape : Level → (indName : Name) → MetaM { l : Level // matchesShape l }

/-- Match an arbitrary level -/
def LevelShape.sortU : LevelShape where
  createLParams _ levelParams := (levelParams.map Level.param, levelParams)
  matchesShape _ := true
  ensureShape l _ := return ⟨l, rfl⟩

/-- Match the level shape `Type u` -/
def LevelShape.typeU : LevelShape where
  createLParams lvl levelParams :=
    let succLevels : NameSet := decLevels lvl {}
    let lparams := levelParams.map fun nm =>
      if succLevels.contains nm then
        .succ (.param nm)
      else
        .param nm
    (lparams, levelParams)
  matchesShape l := l matches .succ _
  ensureShape l indName := do
    let some l := l.dec |
      throwError "Inductive `{.ofConstName indName}` is a predicate, \
        expected a data-carrying inductive"
    return ⟨.succ l, rfl⟩

private def constLevelAssignment : Level → (one : Bool) → NameMap Level → NameMap Level
  | .zero, false, set => set
  | .succ l, true, set => constLevelAssignment l false set
  -- these are invalid configurations but we'll catch them later
  | .zero, true, set => set
  | .succ _, false, set => set
  -- for simplicity, we simply expect both sides of a `max` or `imax` to be equal
  -- at least, we can expect that neither side is syntactically zero because of normalization
  | .max l l', isOne, set => constLevelAssignment l' isOne (constLevelAssignment l isOne set)
  | .imax l l', true, set => constLevelAssignment l' true (constLevelAssignment l true set)
  -- for imax = 0 we only need to check the right-hand side
  | .imax _l l', false, set => constLevelAssignment l' true set
  | .param u, isOne, set => set.insert u (if isOne then .one else .zero)
  | .mvar _, _, _ => unreachable!

/-- Match the level `Type` -/
def LevelShape.type : LevelShape where
  createLParams lvl levelParams :=
    let assignment : NameMap Level := constLevelAssignment lvl (one := true) {}
    let lparams := levelParams.map fun nm =>
      if let some val := assignment.find? nm then
        val
      else
        .param nm
    let levelParams := levelParams.filter (!assignment.contains ·)
    (lparams, levelParams)
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
  createLParams lvl levelParams :=
    let assignment : NameMap Level := constLevelAssignment lvl (one := false) {}
    let lparams := levelParams.map fun nm =>
      if let some val := assignment.find? nm then
        val
      else
        .param nm
    let levelParams := levelParams.filter (!assignment.contains ·)
    (lparams, levelParams)
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
unspecified, it is inferred automatically, using `.sortU`, `.typeU`, `.prop`, `.type` depending on
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
    let mut hasPrivate := false
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
      let (lparams, newLevelParams) := levelShape.createLParams indLevel fstInfo.levelParams
      let mut indLevel' := indLevel.instantiateParams fstInfo.levelParams lparams
      indLevel' ← levelShape.ensureShape indLevel' fstInfo.name
      forallBoundedTelescope (← instantiateTypeLevelParams fstInfo.toConstantVal lparams) nparams fun params _ => do
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
      -- backtrack
      set state
      return false
  return true

/--
For every name provided to the deriving handler, look for an instance of `derivedFrom (name ...)`
and pass both the instance application and its delta-reduced version to `perInstance`.

This function is currently limited to `derivedFrom` type classes that have the type as their only
parameter (and e.g. don't have additional instance assumptions).
-/
def deriveSimpleLawTypeClass (typeClass derivedFrom : Name)
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
        throwError "Failed to derive `{.ofConstName typeClass}` for `{.ofConstName name}`; \
          it is a law type class for `{.ofConstName derivedFrom}` \
          but there is no `{.ofConstName derivedFrom}` instance for `{.ofConstName name}`.\
          {hint}"
      let some instEntry ← chooseInstance instanceEntries |
        throwError "There are multiple `{.ofConstName derivedFrom}` instances for \
          `{.ofConstName name}`, namely: {.andList (instanceEntries.map (·.val)).toList}"
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
            className := typeClass
            levelParams
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
