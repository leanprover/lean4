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

def Lean.mkInstanceNameOfType (type : Expr) : TermElabM Name := do
  let name ← NameGen.mkBaseNameWithSuffix "inst" type
  let name ← liftMacroM <| mkUnusedBaseName name
  let name := (← getCurrNamespace) ++ name
  if (type.find? (·.constName?.any isPrivateName)).isSome then
    return mkPrivateName (← getEnv) name
  else
    return name

def Lean.mkInstance (name : Name) (levelParams : List Name) (type value : Expr)
    (isMeta : Bool) (compile : Bool := true) (prio : Nat := eval_prio default) :
    TermElabM Unit := do
  let env ← getEnv
  let isUnsafe := env.hasUnsafe type || env.hasUnsafe value
  let isProp ← isProp type
  let decl :=
    if isProp then
      if isUnsafe then
        -- recall that theorems can not be unsafe
        .defnDecl {
          name, levelParams, type, value
          hints := .opaque
          safety := .unsafe
        }
      else
        .thmDecl {
          name, levelParams, type, value
        }
    else
      .defnDecl {
        name, levelParams, type, value
        hints := .regular (getMaxHeight env value + 1)
        safety := if isUnsafe then .unsafe else .safe
      }
  withoutExporting (when := isProp || isPrivateName name) do
    addDecl decl
  setReducibilityStatus name .instanceReducible
  addInstance name (if isPrivateName name then .local else .global) prio
  if isMeta && !isProp then
    modifyEnv (markMeta · name)
  unless isProp do
    if compile then
      compileDecl decl (logErrors := !(← read).isNoncomputableSection || isMeta)
    else
      modifyEnv (addNoncomputable · name)
  enableRealizationsForConst name

/--
Creates a new metavariable in the local context `lctx`, reverting any free variables in `ty` that
do not occur in `lctx`. The return value will be an application of the metavariable with the
reverted variables, i.e. a metavariable application of type `ty`.

Note: This function assumes that the `lctx` is a subprefix of the current local context.
-/
def Lean.Meta.mkFreshRevertedMVarAt (ty : Expr) (lctx : LocalContext) (linsts : LocalInstances)
    (kind : MetavarKind := .syntheticOpaque) : MetaM Expr := do
  let ty ← instantiateMVars ty
  let state ← (collectFVars {} ty).addDependencies
  let toRevert := (← getLCtx).getFVarIds.filter (fun f => state.fvarSet.contains f && !lctx.contains f)
  let toRevert := toRevert.map Expr.fvar
  let ty' ← mkForallFVars toRevert ty
  let mvar ← mkFreshExprMVarAt lctx linsts ty' kind (numScopeArgs := toRevert.size)
  return mkAppN mvar toRevert

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

Note: This option only works for deriving handlers that support it, i.e. deriving handlers that use
the `Lean.Meta.Deriving` framework.
-/
register_option deriving.bindersVerbatim : Bool := {
  defValue := false
  descr := "if true, use instance requirements verbatim as instance binders instead of trying to \
    synthesize them in deriving handlers that support this option"
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

Note: This option only works for deriving handlers that support it, i.e. deriving handlers that use
the `Lean.Meta.Deriving` framework.
-/
register_option deriving.reduceInstances : Bool := {
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

Note: This option only works for deriving handlers that support it, i.e. deriving handlers that use
the `Lean.Meta.Deriving` framework.
-/
register_option deriving.strict : Bool := {
  defValue := true
  descr := "if true, reject complex instance hypotheses in deriving handlers"
}

private def isIgnoredConstant (nm : Name) (env : Environment) : Bool :=
  nm == ``Eq || (env.getProjectionFnInfo? nm).any (·.fromClass)

private def goodKeys (keys : Array DiscrTree.Key) (env : Environment) : Bool := Id.run do
  let some (.const _ _) := keys[0]? | return false
  let mut specialFragment : Option DiscrTree.Key := none
  for h : i in 1...keys.size do
    let key := keys[i]
    match key with
    | .const nm _ =>
      if isIgnoredConstant nm env then
        continue
      if specialFragment.isSome then
        return false
      specialFragment := some key
    | .arrow =>
      if specialFragment.isSome then
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

/--
Given an instance type `instType` and a local context `lctx` with associated local instances
`linsts`, try to apply a canonical instance, producing new instance hypotheses as synthetic opaque
metavariables in the provided local context.

The result of this function is a pair of the instance application and the list of new instance
hypotheses together with an indication of whether to run this function again on the resulting
instance obligation. We use a heuristic here to (try to) make sure we don't run into an infinite
loop.

Canonical instances are currently defined as instances with exactly two special fragments in the
discrimination tree keys (forall and constants except `Eq` because of `DecidableEq`). Furthermore,
we only try an instance if it is the only one with "good keys".
-/
def tryApplyCanonicalInstance (instType : Expr) (lctx : LocalContext) (linsts : LocalInstances) :
    MetaM (Option (Expr × Array (MVarId × Bool))) := do
  forallTelescopeReducing (whnfType := true) instType fun vars body => do
    -- try to apply instance
    trace[Elab.Deriving] "Trying to reduce {body}"
    let instances ← getGlobalInstancesIndex
    let matching ← instances.getUnify body
    trace[Elab.Deriving] "Instances: {matching}"
    let env ← getEnv
    let matching := matching.filter fun inst => goodKeys inst.keys env
    trace[Elab.Deriving] "Good instances: {matching}"
    let #[instEntry] := matching | return none
    let some name := instEntry.globalName? | return none
    let c ← mkConstWithFreshMVarLevels name
    let (args, bis, instBody) ← forallMetaTelescopeReducing (← inferType c)
    let mut outVars := #[]
    for arg in args, bi in bis do
      if bi.isInstImplicit then
        if instBody.containsMVar arg.mvarId! then
          continue
        let keys ← DiscrTree.mkPath (← inferType arg)
        let newMVar ← mkFreshRevertedMVarAt (← inferType arg) lctx linsts
        arg.mvarId!.assign newMVar
        outVars := outVars.push (newMVar.getAppFn.mvarId!, goodHypothesisKeys keys env)
    unless ← isDefEqI instBody body do
      trace[Elab.Deriving] "Failed to unify"
      return none
    let c ← instantiateMVars c
    if c.hasLevelMVar then
      trace[Elab.Deriving] "Remaining level metavariables in {c}"
      return none
    let mctx ← getMCtx
    let mut res := c
    for arg in args do
      let arg ← instantiateMVars arg
      -- all metavariables that were there before should be synthetic opaque
      if arg.hasLevelMVar then
        trace[Elab.Deriving] "Remaining level metavariables in {arg}"
        return none
      if arg.hasAnyMVar (fun m => !(mctx.getDecl m).kind.isSyntheticOpaque) then
        trace[Elab.Deriving] "Remaining metavariables in {arg}"
        return none
      res := res.app arg
    return some (← mkLambdaFVars vars res, outVars)

structure Deriving.State where
  instanceMVars : Array MVarId := #[]
  newLInsts : LocalInstances
  -- for documentation purposes
  invariant1 : instanceMVars.size ≤ newLInsts.size := by exact Nat.zero_le _
  invariant2 (i : Nat) (hi : i < instanceMVars.size) :
    newLInsts[i + newLInsts.size - instanceMVars.size].fvar = .mvar instanceMVars[i] := by nofun

structure Deriving.Context where
  /-- Level parameters for the instances -/
  levelParams : List Name
  /-- Parameters for the instances. These should be free variables -/
  params : Array Expr
  /-- The local context that contains all `params` -/
  paramLCtx : LocalContext
  /-- The local instances for `paramLCtx` -/
  paramLInsts : LocalInstances
  /-- One inductive in the mutual group -/
  indInfo : InductiveVal
  /-- Level parameters for the inductive type -/
  lparams : List Level
  /--
  Parameters (and potentially indices) for the inductive type. By default, this coincides with
  `params` but this doesn't have to be the case in general. These have to type-check in `paramLCtx`.
  -/
  indParams : Array Expr
  /--
  The resulting level for the mutual inductive type, i.e.
  `mkAppN (mkAppN (.const indInfo.name lparams) indParams) indIndices : Sort indLevel`
  for any indices. In the case of `mkInductiveDerivingHandler (isSucc := true)`, this is guaranteed
  to syntactically be `.succ lvl` for some `lvl`.
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

nonrec def DerivingM.run (x : DerivingM α) (ctx : Deriving.Context) : TermElabM α :=
  (x.run ctx).run' { newLInsts := ctx.paramLInsts }

private def pushInstanceHypothesis (goal : MVarId) (className : Name) : DerivingM Unit := do
  -- We simply add the new metavariables as local instances for instance synthesis to pick up
  -- That way we can detect redundant instances more easily
  modify fun state => {
    state with
    instanceMVars := state.instanceMVars.push goal
    newLInsts := state.newLInsts.push { className, fvar := .mvar goal }
    invariant1 := by simpa using state.invariant1
    invariant2 i hi := by
      have := state.invariant1
      rw [Array.size_push] at hi
      simp only [Array.size_push, ← Nat.add_assoc, Nat.add_sub_add_right]
      rcases Nat.lt_add_one_iff_lt_or_eq.mp hi with hlt | rfl
      · rw [Array.getElem_push_lt (by omega), state.invariant2 i hlt, Array.getElem_push_lt hlt]
      · rw [Array.getElem_push_eq, Array.getElem_push, dite_eq_right (by omega)]
  }

def containsRecursiveDecl (e : Expr) : DerivingM Bool := do
  let ctx ← read
  let all := ctx.indInfo.all
  return (e.find? fun | .const nm _ => nm ∈ all | _ => false).isSome

private def trySynthesize (type : Expr) : DerivingM (Option Expr) := do
  unless deriving.bindersVerbatim.get (← getOptions) do
    return (← trySynthInstance type).toOption
  let some className ← isClass? type |
    throwError "type class instance expected{indentExpr type}"
  for inst in (← getLocalInstances) do
    if inst.className == className then
      if ← isDefEqI (← inferType inst.fvar) type then
        return inst.fvar
  return none

private partial def processInstanceHypothesis (mvar : MVarId)
    (allowCanonicalInstanceReduction : Bool := true) : DerivingM Unit := withIncRecDepth do
  let type ← mvar.getType
  let some className ← isClass? type |
    -- if this wasn't reported before, report now
    throwError "type class instance expected{indentExpr type}"
  if let some res ← withLCtx (← read).paramLCtx (← get).newLInsts (trySynthesize type) then
    mvar.assign res
    return
  let mut shouldTry := allowCanonicalInstanceReduction -- avoid loops
  if !deriving.reduceInstances.get (← getOptions) ||
      deriving.bindersVerbatim.get (← getOptions) then
    shouldTry := false
  unless shouldTry do
    -- if the instance requirement is nested (i.e. contains recursive occurrences),
    -- we *have* to reduce it, otherwise we end up with a useless instance like
    -- `instance [BEq (List Thing)] : BEq Thing`
    unless ← containsRecursiveDecl type do
      return ← pushInstanceHypothesis mvar className
    -- also, try instance synthesis even if it was disabled through `deriving.bindersVerbatim`
    if let some res ← withLCtx (← read).paramLCtx (← get).newLInsts (trySynthesize type) then
      mvar.assign res
      return
  let mctx ← getMCtx
  -- try reducing e.g. `BEq (List α)` to `BEq α`
  let res ← tryApplyCanonicalInstance type (← getLCtx) (← getLocalInstances)
  if let some (assignment, outVars) := res then
    mvar.assign assignment
    for (var, allow) in outVars do
      processInstanceHypothesis var allow
  else
    if ← containsRecursiveDecl type then
      throwError "Got stuck at instance requirement for nested type:{indentExpr type}"
    setMCtx mctx
    pushInstanceHypothesis mvar className

def synthInstanceDeriving (e : Expr) : DerivingM Expr := do
  if let some res ← withLCtx (← getLCtx) (← get).newLInsts (trySynthesize e) then
    return res
  let mvarApp ← mkFreshRevertedMVarAt e (← read).paramLCtx (← read).paramLInsts
  withLCtx (← read).paramLCtx (← read).paramLInsts do
    processInstanceHypothesis mvarApp.getAppFn.mvarId!
  instantiateMVars mvarApp

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
  let m := state.newLInsts.size
  let lctx ← getLCtx
  let mut oldLInsts : Vector LocalInstance m := ⟨state.newLInsts, rfl⟩
  let mut newLInsts : Vector LocalInstance m := ⟨state.newLInsts, rfl⟩
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
  let mut complexHyps := #[]
  for mvar in instanceHyps do
    let type ← mvar.getType
    withReducible do←
    forallTelescopeReducing type (whnfType := true) fun _ body => do←
      let path ← DiscrTree.mkPath body
      unless goodHypothesisKeys path (← getEnv) do
        complexHyps := complexHyps.push type
  unless complexHyps.isEmpty do
    let note := .note m!"This usually indicates a missing instance that can be derived using \
      `deriving instance ClassName for TypeName`. If this is however intentional, you can disable \
      this error using `set_option deriving.strict false`"
    throwError "While deriving an instance, the following complex instance requirements \
      were encountered that could not be synthesized:\
      {indentD (.andList (complexHyps.toList.map (m!"[{·}]")))}{note}"

def produceInstanceHyps : DerivingM (Array Expr) := do
  let filtered ← withLCtx (← read).paramLCtx (← read).paramLInsts do
    filterInstanceObligations (← get)
  if deriving.strict.get (← getOptions) && !deriving.bindersVerbatim.get (← getOptions) &&
      deriving.reduceInstances.get (← getOptions) then
    checkInstanceHypotheses filtered
  return filtered.map Expr.mvar

def mkInstanceForDeriving (instanceHyps : Array Expr) (type value : Expr) : DerivingM Unit := do
  let allVars := (← read).params ++ instanceHyps
  let instName ← mkInstanceNameOfType type
  let type ← instantiateMVars <| ← mkForallFVars allVars (← instantiateMVars type) (binderInfoForMVars := .instImplicit)
  let value ← instantiateMVars <| ← mkLambdaFVars allVars (← instantiateMVars value) (binderInfoForMVars := .instImplicit)
  let shouldExpose := (value.find? (·.constName?.any isPrivateName)).isNone
  withExporting (isExporting := shouldExpose) do
    mkInstance instName (← read).levelParams type value (← read).isMeta

def isRecursive : DerivingM Bool := do
  return (← read).indInfo.isRec

def isNested : DerivingM Bool := do
  return (← read).indInfo.isNested

def eliminatesToProp : DerivingM Bool := do
  let recInfo ← getConstInfoRec (mkRecName (← read).indInfo.name)
  return recInfo.levelParams.length == (← read).indInfo.levelParams.length

def deriveTransformationInstPerConstructor (className : Name)
    (perCtor : InductiveVal → ConstructorVal → Array Expr → DerivingM Expr) :
    DerivingM Bool := do
  -- Step 1: Figure out the details for the class
  if ← eliminatesToProp then
    return false
  let classInfo ← getConstInfoInduct className
  unless classInfo.numCtors = 1 ∧ ¬ classInfo.isRec ∧ classInfo.numIndices = 0 do
    throwError "Invalid use of `deriveSimpleInstPerConstructor`, \
      expected {.ofConstName className} to be a structure"
  unless classInfo.numParams = 1 ∧ classInfo.levelParams.length = 1 do
    throwError "Invalid use of `deriveSimpleInstPerConstructor`, \
      expected {.ofConstName className} to have exactly one parameter and one level parameter"
  let [ctor] := classInfo.ctors | unreachable!
  let [u] := classInfo.levelParams | unreachable!
  let ctorVal ← getConstInfoCtor ctor
  unless ctorVal.numFields = 1 do
    throwError "Invalid use of `deriveSimpleInstPerConstructor`, \
      expected {.ofConstName className} to have exactly one field"
  let .forallE _ (.sort univ) (.forallE fieldName (.forallE _ (.bvar 0) tgt _) _ _) _ := ctorVal.type |
    throwError "Invalid use of `deriveSimpleInstPerConstructor`, \
      expected field of {.ofConstName className} to have the shape \
      `α → β` where `α` is the type parameter"
  if tgt.hasLooseBVars then
    throwError "Invalid use of `deriveSimpleInstPerConstructor`, expected target type of field of
      {.ofConstName className} to be nondependent"
  let tgtSort ← getLevel tgt
  let onlyType ←
    if univ == .param u then
      pure false
    else if univ == .succ (.param u) then
      pure true
    else
      throwError "Invalid use of `deriveSimpleInstPerConstructor`, expected type parameter to be \
        either fully universe polymorphic or `Type`-polymorphic"
  let mut paramLevel := (← read).indLevel
  if onlyType then
    paramLevel ← decLevel paramLevel
  -- Step 2: Create `recVars`
  let all := (← read).indInfo.all.toArray
  let instanceTypes ← all.mapM fun name => do
    let typeApp := mkAppN (.const name (← read).lparams) (← read).indParams
    forallTelescopeReducing (← inferType typeApp) fun indices _ => do
      mkForallFVars indices <| .app (.const className [paramLevel]) (mkAppN typeApp indices)
  let infos := instanceTypes.mapIdx fun idx ty => ((`recinst).appendIndexAfter (idx + 1), ty)
  withLocalDeclsDND infos fun recVars => do
  -- Step 3: Compute types and values
  let mut typesAndValues : Array (Expr × Expr) := #[]
  for name in all do
    let info ← getConstInfoInduct name
    let casesOnApp := mkAppN (.const (mkCasesOnName name) (tgtSort :: (← read).lparams)) (← read).indParams
    let casesOnType ← inferType casesOnApp
    let .forallE _ motiveType body _ := casesOnType | unreachable!
    typesAndValues := typesAndValues.push <| ← forallTelescope motiveType fun vars _ => do
      let motive ← mkLambdaFVars vars tgt
      let body := body.instantiate1 motive
      let mut body ← instantiateForall body vars
      let mut casesOnApp := mkAppN (casesOnApp.app motive) vars
      for ctor in info.ctors do
        let .forallE _ altType body' _ := body | unreachable!
        let ctorInfo ← getConstInfoCtor ctor
        let minor ← forallBoundedTelescope altType ctorInfo.numFields fun fields _ => do
          mkLambdaFVars fields <| ← perCtor info ctorInfo fields
        casesOnApp := casesOnApp.app minor
        body := body'
      return (← mkForallFVars vars tgt, ← mkLambdaFVars vars casesOnApp)
  let instanceHyps ← produceInstanceHyps
  let instanceTypes ← instanceTypes.mapM fun e => mkForallFVars instanceHyps e (binderInfoForMVars := .instImplicit)
  let instNames ← instanceTypes.mapM fun ty => mkInstanceNameOfType ty
  -- Step 4: Assign the `recVars`
  let ourLParams := (← read).levelParams.map Level.param
  let recVarValues ← all.mapIdxM fun idx name => do
    let typeApp := mkAppN (.const name (← read).lparams) (← read).indParams
    forallTelescopeReducing (← inferType typeApp) fun indices _ => do
      let recApp := .const (instNames[idx]! ++ fieldName) ourLParams
      let recApp := mkAppN recApp (← read).indParams
      let recApp := mkAppN recApp instanceHyps
      let recApp := mkAppN recApp indices
      let inst : Expr := mkApp2 (.const ctor [paramLevel]) (mkAppN typeApp indices) recApp
      mkLambdaFVars indices inst
  -- Step 5: Create pre-definitions
  let predefs : Array PreDefinition ← typesAndValues.mapIdxM fun idx (ty, val) => do
    let val := (← instantiateMVars val).replaceFVars recVars recVarValues
    let ty ← mkForallFVars instanceHyps ty (binderInfoForMVars := .instImplicit)
    let val ← mkLambdaFVars instanceHyps val (binderInfoForMVars := .instImplicit)
    let instName := instNames[idx]!
    return {
      ref := ← getRef
      kind := .def
      levelParams := (← read).levelParams
      modifiers := {
        recKind := .partial
      }
      declName := instName ++ fieldName
      binders := .missing
      type := ← mkForallFVars (← read).params ty
      value := ← mkLambdaFVars (← read).params val
      termination := .none
    }
  withoutExporting do
    addPreDefinitions ({}, {}) predefs
  -- Step 6: Create instances
  let nameSet : NameSet := .ofArray (← read).names
  let allParams := (← read).params ++ instanceHyps
  for name in all, instName in instNames, ty in instanceTypes, recVarValue in recVarValues do
    unless nameSet.contains name do continue
    let value ← mkLambdaFVars allParams recVarValue (binderInfoForMVars := .instImplicit)
    withExporting do
      mkInstance instName (← read).levelParams (← mkForallFVars (← read).params ty) value
        (← read).isMeta
  return true

private def decLevels : Level → NameSet → Option NameSet
  | .zero, _ => none -- can only happen at the top level because of normalization
  | .succ _, set => some set
  | .max l l', set => (decLevels l set).bind (decLevels l')
  | .imax l l', set => (decLevels l set).bind (decLevels l')
  | .param u, set => some (set.insert u)
  | .mvar _, _ => unreachable!

def mkInductiveDerivingHandler (perMutualBlock : DerivingM Bool) (needSucc : Bool) :
    DerivingHandler := fun names => do
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
  for names in blocks do
    let fstInfo ← getConstInfoInduct names[0]!
    let nparams := fstInfo.numParams
    let res ← liftTermElabM do
      let indLevel ← forallTelescopeReducing (whnfType := true) fstInfo.type fun _ body => do
        let .sort lvl := body | throwError "Unexpected inductive type type{indentExpr fstInfo.type}"
        pure lvl.normalize
      let mut succLevels : NameSet := {}
      if needSucc then
        let some lvls := decLevels indLevel succLevels |
          throwError "Inductive `{.ofConstName fstInfo.name}` is a predicate, expected a data-carrying inductive"
        succLevels := lvls
      let lparams : List Level := fstInfo.levelParams.map fun nm =>
        if succLevels.contains nm then
          .succ (.param nm)
        else
          .param nm
      let mut indLevel' := indLevel.instantiateParams fstInfo.levelParams lparams
      if needSucc then
        let some indLevelSucc := indLevel'.dec | unreachable!
        indLevel' := .succ indLevelSucc
      forallBoundedTelescope (← instantiateTypeLevelParams fstInfo.toConstantVal lparams) nparams fun params _ => do
        let ctx := {
          levelParams := fstInfo.levelParams
          params := params
          paramLCtx := ← getLCtx
          paramLInsts := ← getLocalInstances
          indInfo := fstInfo
          lparams := lparams
          indParams := params
          indLevel := indLevel'
          names := names
          isMeta := names.all (isMarkedMeta (← getEnv))
        }
        perMutualBlock.run ctx
    unless res do
      -- backtrack
      set state
      return false
  return true

def deriveSimpleLawTypeClass (derivedFrom : Name)
    (perInstance : (inst : Expr) → (instValue : Expr) → DerivingM Bool) :
    DerivingHandler := fun names => liftTermElabM do
  let instances ← getGlobalInstancesIndex
  for name in names do
    let some info ← isInductive? name | return false
    let arity := info.numParams + info.numIndices
    let instanceEntries := instances.getEntriesWithKeys
      (#[.const derivedFrom 1, .const name arity] ++ Array.replicate arity .star)
    if instanceEntries.isEmpty then
      throwError "There is no `{.ofConstName derivedFrom}` instance for `{.ofConstName name}`"
    let #[instEntry] := instanceEntries |
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
          levelParams
          params := vars
          paramLCtx := ← getLCtx
          paramLInsts := ← getLocalInstances
          indInfo := info
          lparams := indFn.constLevels!
          indParams := indArgs
          indLevel := ← getLevel indApp
          names := #[name]
          isMeta := isMarkedMeta (← getEnv) name
        }
        (perInstance instApp instValue).run ctx
    unless res do
      return false
  return true

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
      if instanceEntries.isEmpty then
        needToDerive := needToDerive.push name
    return needToDerive
  preHandler prereqNames <&&> handler names

end Lean.Meta.Deriving
