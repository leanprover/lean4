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
    (isMeta : Bool := false) (compile : Bool := true)
    (prio : Nat := eval_prio default) : TermElabM Unit := do
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
reverted variables.

Note: This function assumes that the `lctx` is a subprefix of the current local context.
-/
def Lean.Meta.mkFreshRevertedMVarAt (ty : Expr) (lctx : LocalContext) (linsts : LocalInstances) :
    MetaM Expr := do
  let ty ← instantiateMVars ty
  let state ← (collectFVars {} ty).addDependencies
  let toRevert := (← getLCtx).getFVarIds.filter (fun f => state.fvarSet.contains f && !lctx.contains f)
  let toRevert := toRevert.map Expr.fvar
  let ty' ← mkForallFVars toRevert ty
  let mvar ← mkFreshExprMVarAt lctx linsts ty' .syntheticOpaque
  return mkAppN mvar toRevert

namespace Lean.Meta.Deriving

private def goodKeys (keys : Array DiscrTree.Key) : Bool := Id.run do
  let some (.const _ _) := keys[0]? | return false
  let mut constFragment : Option Name := none
  for h : i in 1...keys.size do
    match keys[i] with
    | .const nm _ =>
      if nm == ``Eq then
        -- hack for `DecidableEq`
        continue
      if constFragment.isSome then
        return false
      constFragment := some nm
    | .star => continue
    | _ => return false
  return constFragment.isSome

private def goodOutputKeys (keys : Array DiscrTree.Key) : Bool := Id.run do
  let some (.const _ _ : DiscrTree.Key) := keys[0]? | return false
  return keys.all (start := 1) (· matches .star | .const ``Eq _)

/--
Given a list of metavariables corresponding to instance obligations, returns a suitable list of
instance assumptions to be used in `mkLambdaFVars (binderInfoForMVars := .instImplicit)`.

Precondition: The current local context must be a prefix of the local contexts of
all metavariables.
-/
def filterInstanceObligations (mvars : Array MVarId) : MetaM (Array MVarId) := do
  let mut newMVars : Array MVarId := #[]
  let mut stack : Array (MVarId × Bool) := mvars.reverse.map (·, true)
  let origLInsts ← getLocalInstances
  let mut lctx ← getLCtx
  let mut linsts ← getLocalInstances
  let mut timeout := 100
  while h : !stack.isEmpty do
    let (back, allowCanonicalInstanceReduction) := stack.back (by simp_all [Array.size_pos_iff])
    stack := stack.pop
    let type ← back.getType
    let some className ← isClass? type |
      -- if this wasn't reported before, report now
      throwError "type class instance expected{indentExpr type}"
    if let .some res ← withLCtx lctx linsts (trySynthInstance type) then
      back.assign res
      continue
    unless allowCanonicalInstanceReduction do
      -- avoid loops
      newMVars := newMVars.push back
      -- we simply add the new metavariables as local instances for instance synthesis to pick up
      -- that way we can detect redundant instances more effectively
      linsts := linsts.push { className, fvar := .mvar back }
      continue
    -- This step tries to reduce e.g. `BEq (List α)` to `BEq α`
    let mctx ← getMCtx
    let res ← forallTelescopeReducing (whnfType := true) type fun vars body => do
      -- try to apply instance
      trace[Elab.Deriving] "Trying to reduce {body}"
      let instances ← getGlobalInstancesIndex
      let matching ← instances.getUnify body
      trace[Elab.Deriving] "Instances: {matching}"
      let matching := matching.filter fun inst => goodKeys inst.keys
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
          let newMVar ← mkFreshRevertedMVarAt (← inferType arg) lctx origLInsts
          arg.mvarId!.assign newMVar
          outVars := outVars.push (newMVar.getAppFn.mvarId!, goodOutputKeys keys)
      unless ← isDefEqI instBody body do
        trace[Elab.Deriving] "Failed to unify"
        return none
      let c ← instantiateMVars c
      if c.hasLevelMVar then
        trace[Elab.Deriving] "Remaining level metavariables in {c}"
        return none
      let mctx' ← getMCtx
      let mut res := c
      for arg in args, bi in bis do
        let arg ← instantiateMVars arg
        -- all metavariables that were there before should be synthetic opaque
        if arg.hasLevelMVar then
          trace[Elab.Deriving] "Remaining level metavariables in {arg}"
          return none
        if arg.hasAnyMVar (fun m => !(mctx'.getDecl m).kind.isSyntheticOpaque) then
          trace[Elab.Deriving] "Remaining metavariables in {arg}"
          return none
        res := res.app arg
      back.assign (← mkLambdaFVars vars res)
      return some outVars
    if let some outVars := res then
      stack := outVars.foldr (fun x as => as.push x) stack
    else
      setMCtx mctx
      newMVars := newMVars.push back
      linsts := linsts.push { className, fvar := .mvar back }
  return newMVars

structure Deriving.State where
  instanceMVars : Array MVarId := #[]

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

abbrev DerivingM := ReaderT Deriving.Context <| StateRefT Deriving.State TermElabM

def synthInstanceDeriving (e : Expr) : DerivingM Expr := do
  if let .some res ← trySynthInstance e then
    return res
  let state ← (collectFVars {} e).addDependencies
  let paramLCtx := (← read).paramLCtx
  let deps := (← getLCtx).getFVarIds.filter fun f => !paramLCtx.contains f && state.fvarSet.contains f
  let deps := deps.map Expr.fvar
  let mvar ← mkFreshExprMVarAt (← read).paramLCtx (← read).paramLInsts
    (← mkForallFVars deps e) .syntheticOpaque
  modify fun state => { state with instanceMVars := state.instanceMVars.push mvar.mvarId! }
  return mkAppN mvar deps

def produceInstanceHyps : DerivingM (Array Expr) := do
  let instMVars := (← get).instanceMVars
  let filtered ← withLCtx (← read).paramLCtx (← read).paramLInsts do
    filterInstanceObligations instMVars
  return filtered.map Expr.mvar

def mkInstanceForDeriving (instanceHyps : Array Expr) (type value : Expr) : DerivingM Unit := do
  let allVars := (← read).params ++ instanceHyps
  let instName ← mkInstanceNameOfType type
  let type ← instantiateMVars <| ← mkForallFVars allVars (← instantiateMVars type) (binderInfoForMVars := .instImplicit)
  let value ← instantiateMVars <| ← mkLambdaFVars allVars (← instantiateMVars value) (binderInfoForMVars := .instImplicit)
  let shouldExpose := (value.find? (·.constName?.any isPrivateName)).isNone
  withExporting (isExporting := shouldExpose) do
    discard <| mkInstance instName (← read).levelParams type value

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
  logInfo instanceHyps
  let predefs : Array PreDefinition ← typesAndValues.mapIdxM fun idx (ty, val) => do
    let val := (← instantiateMVars val).replaceFVars recVars recVarValues
    let ty ← mkForallFVars instanceHyps ty (binderInfoForMVars := .instImplicit)
    let val ← mkLambdaFVars instanceHyps val (binderInfoForMVars := .instImplicit)
    logInfo ty
    logInfo val
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
        (isMeta := isMarkedMeta (← getEnv) name)
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
        }
        (perMutualBlock.run ctx).run' {}
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
        }
        (perInstance instApp instValue ctx).run' {}
    unless res do
      return false
  return true

end Lean.Meta.Deriving
