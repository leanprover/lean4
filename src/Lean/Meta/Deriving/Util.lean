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

namespace Lean.Meta.Deriving

/--
Given a list of metavariables corresponding to instance obligations, returns a suitable list of
instance assumptions to be used in `mkLambdaFVars (binderInfoForMVars := .instImplicit)`.

Precondition: The current local context must be a prefix of the local contexts of
all metavariables.
-/
def filterInstanceObligations (mvars : Array MVarId) : MetaM (Array MVarId) := do
  -- Do all sorts of filtering things
  return mvars

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
  Parameters for the inductive type. By default, this coincides with `params` but this doesn't
  have to be the case in general. These have to type-check in `paramLCtx`.
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
  let type ← mkForallFVars allVars type (binderInfoForMVars := .instImplicit)
  let value ← mkLambdaFVars allVars value (binderInfoForMVars := .instImplicit)
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

end Lean.Meta.Deriving
