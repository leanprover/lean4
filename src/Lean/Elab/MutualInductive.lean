/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Kyle Miller
-/
prelude
import Lean.Util.ForEachExprWhere
import Lean.Util.ReplaceLevel
import Lean.Util.ReplaceExpr
import Lean.Util.CollectLevelParams
import Lean.Meta.Constructions
import Lean.Meta.CollectFVars
import Lean.Meta.SizeOf
import Lean.Meta.Injective
import Lean.Meta.IndPredBelow
import Lean.Elab.Command
import Lean.Elab.ComputedFields
import Lean.Elab.DefView
import Lean.Elab.DeclUtil
import Lean.Elab.Deriving.Basic
import Lean.Elab.DeclarationRange

/-!
# Elaborator framework for (mutual) inductives

This module defines the framework for elaborating (mutually recursive) inductive types.
Commands such as `inductive` and `structure` plug into this framework,
and the framework orchestrates their mutual elaboration.

The main entry point for new inductive commands are the `@[builtin_inductive_elab]`/`@[inductive_elab]` attributes,
which register a handler for a given decl syntax.

The main entry point to elaboration are the functions
* `Lean.Elab.Command.isInductiveCommand` to determine whether syntax has a registered inductive elaborator.
* `Lean.Elab.Command.elabInductives` to elaborate a list of syntaxes as mutually inductive types.
* `Lean.Elab.Command.elabInductive` to elaborate a single inductive command.

For `mutual ... end` in particular:
* `Lean.Elab.Command.isMutualInductive` to check whether each syntax element of a `mutual ... end` block has a registered inductive elaborator.
* `Lean.Elab.Command.elabMutualInductive` to elaborate a list of syntaxes satisfying `isMutualInductive` as a mutually inductive block.

See the docstring on `Lean.Elab.Command.InductiveElabDescr` for an overview of the framework.
-/

namespace Lean.Elab.Command
open Meta

builtin_initialize
  registerTraceClass `Elab.inductive

register_builtin_option inductive.autoPromoteIndices : Bool := {
  defValue := true
  descr    := "Promote indices to parameters in inductive types whenever possible."
}

register_builtin_option bootstrap.inductiveCheckResultingUniverse : Bool := {
  defValue := true,
  group    := "bootstrap",
  descr    := "by default the `inductive`/`structure` commands report an error if the resulting universe is not zero, \
    but may be zero for some universe parameters. Reason: unless this type is a subsingleton, \
    it is hardly what the user wants since it can only eliminate into `Prop`. \
    In the `Init` package, we define subsingletons, and we use this option to disable the check. \
    This option may be deleted in the future after we improve the validator"
}

/-- View of a constructor. Only `ref`, `modifiers`, `declName`, and `declId` are required by the mutual inductive elaborator itself. -/
structure CtorView where
  /-- Syntax for the whole constructor. -/
  ref       : Syntax
  modifiers : Modifiers
  /-- Fully qualified name of the constructor. -/
  declName  : Name
  /-- Syntax for the name of the constructor, used to apply terminfo. If the source is synthetic, terminfo is not applied. -/
  declId    : Syntax
  /-- For handler use. The `inductive` uses it for the binders to the constructor. -/
  binders   : Syntax := .missing
  /-- For handler use. The `inductive` command uses it for the resulting type for the constructor. -/
  type?     : Option Syntax := none
  deriving Inhabited

structure ComputedFieldView where
  ref       : Syntax
  modifiers : Syntax
  fieldId   : Name
  type      : Syntax.Term
  matchAlts : TSyntax ``Parser.Term.matchAlts

/-- A view for generic inductive types. -/
structure InductiveView where
  ref             : Syntax
  declId          : Syntax
  modifiers       : Modifiers
  isClass         : Bool
  /-- Whether the command should allow indices (like `inductive`) or not (like `structure`). -/
  allowIndices    : Bool
  /-- Whether the command supports creating inductive types that can be polymorphic across both `Prop` and `Type _`.
  If false, then either the universe must be `Prop` or it must be of the form `Type _`. -/
  allowSortPolymorphism : Bool
  shortDeclName   : Name
  declName        : Name
  levelNames      : List Name
  binders         : Syntax
  type?           : Option Syntax
  ctors           : Array CtorView
  computedFields  : Array ComputedFieldView
  derivingClasses : Array DerivingClassView
  deriving Inhabited

/-- Elaborated header for an inductive type before fvars for each inductive are added to the local context. -/
structure PreElabHeaderResult where
  view       : InductiveView
  lctx       : LocalContext
  localInsts : LocalInstances
  levelNames : List Name
  params     : Array Expr
  type       : Expr
  deriving Inhabited

/-- The elaborated header with the `indFVar` registered for this inductive type. -/
structure ElabHeaderResult extends PreElabHeaderResult where
  indFVar    : Expr
  deriving Inhabited

/-- An intermediate step for mutual inductive elaboration. See `InductiveElabDescr`. -/
structure InductiveElabStep2 where
  /-- The constructors produced by `InductiveElabStep1`. -/
  ctors : List Constructor
  /-- Function to collect additional fvars that might be missed by the constructors.
  It is permissible to include fvars that do not exist in the local context (`structure` for example includes its field fvars). -/
  collectUsedFVars : StateRefT CollectFVars.State MetaM Unit := pure ()
  /-- Function to check universes and provide a custom error. (`structure` uses this to do checks per field to give nicer messages.) -/
  checkUniverses (numParams : Nat) (u : Level) : TermElabM Unit := pure ()
  /-- Step to finalize term elaboration, done immediately after universe level processing is complete. -/
  finalizeTermElab : TermElabM Unit := pure ()
  /-- Like `finalize`, but occurs before `afterTypeChecking` attributes. -/
  prefinalize (levelParams : List Name) (params : Array Expr) (replaceIndFVars : Expr → MetaM Expr) : TermElabM Unit := fun _ _ _ => pure ()
  /-- Finalize the inductive type, after they are all added to the environment, after auxiliary definitions are added, and after computed fields are registered. -/
  finalize (levelParams : List Name) (params : Array Expr) (replaceIndFVars : Expr → MetaM Expr) : TermElabM Unit := fun _ _ _ => pure ()
  deriving Inhabited

/-- An intermediate step for mutual inductive elaboration. See `InductiveElabDescr`. -/
structure InductiveElabStep1 where
  view : InductiveView
  elabCtors (rs : Array ElabHeaderResult) (r : ElabHeaderResult) (params : Array Expr) : TermElabM InductiveElabStep2
  deriving Inhabited

/--
Descriptor for a command processor that elaborates an inductive type.

Elaboration occurs in the following steps:
- Every command has its `mkInductiveView` evaluated, producing `InductiveView`s and callbacks
  for the next steps (all recorded in `InductiveElabStep1`).
- Each `InductiveView` gets elaborated, creating `ElabHeaderResult`s, and the local contexts are unified into a single one
  with a consistent set of parameters between each inductive.
- Each callback is called to elaborate each inductives' constructors and some additional callbacks
  (all recorded in `InductiveElabStep2`).
- Fvars are collected from the constructors and from the `InductiveStep2.collectUsedFVars` callbacks.
  This is used to compute the final set of scoped variables that should be used as additional parameters.
- Universe levels are checked. Commands can give custom errors using `InductiveStep2.collectUniverses`.
- Elaboration of constructors is finalized, with additional tasks done by each `InductiveStep2.collectUniverses`.
- The inductive family is added to the environment and is checked by the kernel.
- Attributes and other finalization activities are performed, including those defined
  by `InductiveStep2.prefinalize` and `InductiveStep2.finalize`.
-/
structure InductiveElabDescr where
  mkInductiveView : Modifiers → Syntax → TermElabM InductiveElabStep1
  deriving Inhabited

/--
Environment extension to register inductive type elaborator commands.
-/
builtin_initialize inductiveElabAttr : KeyedDeclsAttribute InductiveElabDescr ←
  unsafe KeyedDeclsAttribute.init {
    builtinName := `builtin_inductive_elab,
    name := `inductive_elab,
    descr    := "Register an elaborator for inductive types",
    valueTypeName := ``InductiveElabDescr
  }

/--
Returns true if the syntax partipates in the mutual inductive elaborator.
These do not need to be commands. In fact `inductive` and `structure` are registered
on the `Lean.Parser.Command.inductive` and `Lean.Parser.Command.structure` syntaxes.
-/
def isInductiveCommand [Monad m] [MonadEnv m] (stx : Syntax) : m Bool := do
  let env ← getEnv
  return !(inductiveElabAttr.getEntries env stx.getKind).isEmpty

/--
Initializes the elaborator associated to the given syntax.
-/
def mkInductiveView (modifiers : Modifiers) (stx : Syntax) : TermElabM InductiveElabStep1 := do
  let handlers := inductiveElabAttr.getValues (← getEnv) stx.getKind
  if handlers.isEmpty then
    throwErrorAt stx "no '@[inductive_elab]' for '{.ofConstName stx.getKind}'"
  handlers[0]!.mkInductiveView modifiers stx

def checkValidInductiveModifier [Monad m] [MonadError m] (modifiers : Modifiers) : m Unit := do
  if modifiers.isNoncomputable then
    throwError "invalid use of 'noncomputable' in inductive declaration"
  if modifiers.isPartial then
    throwError "invalid use of 'partial' in inductive declaration"

def checkValidCtorModifier [Monad m] [MonadError m] (modifiers : Modifiers) : m Unit := do
  if modifiers.isNoncomputable then
    throwError "invalid use of 'noncomputable' in constructor declaration"
  if modifiers.isPartial then
    throwError "invalid use of 'partial' in constructor declaration"
  if modifiers.isUnsafe then
    throwError "invalid use of 'unsafe' in constructor declaration"
  if modifiers.attrs.size != 0 then
    throwError "invalid use of attributes in constructor declaration"

private def checkUnsafe (rs : Array PreElabHeaderResult) : TermElabM Unit := do
  let isUnsafe := rs[0]!.view.modifiers.isUnsafe
  for r in rs do
    unless r.view.modifiers.isUnsafe == isUnsafe do
      throwErrorAt r.view.ref "invalid inductive type, cannot mix unsafe and safe declarations in a mutually inductive datatypes"

private def checkClass (rs : Array PreElabHeaderResult) : TermElabM Unit := do
  if rs.size > 1 then
    for r in rs do
      if r.view.isClass then
        throwErrorAt r.view.ref "invalid inductive type, mutual classes are not supported"

private def checkNumParams (rs : Array PreElabHeaderResult) : TermElabM Nat := do
  let numParams := rs[0]!.params.size
  for r in rs do
    unless r.params.size == numParams do
      throwErrorAt r.view.ref "invalid inductive type, number of parameters mismatch in mutually inductive datatypes"
  return numParams

private def mkTypeFor (r : PreElabHeaderResult) : TermElabM Expr := do
  withLCtx r.lctx r.localInsts do
    mkForallFVars r.params r.type

/--
Execute `k` with updated binder information for `xs`. Any `x` that is explicit becomes implicit.
-/
def withExplicitToImplicit (xs : Array Expr) (k : TermElabM α) : TermElabM α := do
  let mut toImplicit := #[]
  for x in xs do
    if (← getFVarLocalDecl x).binderInfo.isExplicit then
      toImplicit := toImplicit.push (x.fvarId!, BinderInfo.implicit)
  withNewBinderInfos toImplicit k

/--
Auxiliary function for checking whether the types in mutually inductive declaration are compatible.
-/
private def checkParamsAndResultType (type firstType : Expr) (numParams : Nat) : TermElabM Unit := do
  try
    forallTelescopeCompatible type firstType numParams fun _ type firstType =>
    forallTelescopeReducing type fun _ type =>
    forallTelescopeReducing firstType fun _ firstType => do
      let type ← whnfD type
      match type with
      | .sort .. =>
        unless (← isDefEq firstType type) do
          throwError "resulting universe mismatch, given{indentExpr type}\nexpected type{indentExpr firstType}"
      | _ =>
        throwError "unexpected inductive resulting type"
  catch
    | Exception.error ref msg => throw (Exception.error ref m!"invalid mutually inductive types, {msg}")
    | ex => throw ex

/--
Auxiliary function for checking whether the types in mutually inductive declaration are compatible.
-/
private def checkHeaders (rs : Array PreElabHeaderResult) (numParams : Nat) (i : Nat) (firstType? : Option Expr) : TermElabM Unit := do
  if h : i < rs.size then
    let type ← checkHeader rs[i] numParams firstType?
    checkHeaders rs numParams (i+1) type
where
  checkHeader (r : PreElabHeaderResult) (numParams : Nat) (firstType? : Option Expr) : TermElabM Expr := do
    let type ← mkTypeFor r
    match firstType? with
    | none           => return type
    | some firstType =>
      withRef r.view.ref <| checkParamsAndResultType type firstType numParams
      return firstType

private def elabHeadersAux (views : Array InductiveView) (i : Nat) (acc : Array PreElabHeaderResult) : TermElabM (Array PreElabHeaderResult) :=
  Term.withAutoBoundImplicitForbiddenPred (fun n => views.any (·.shortDeclName == n)) do
    if h : i < views.size then
      let view := views[i]
      let acc ← withRef view.ref <| Term.withAutoBoundImplicit <| Term.elabBinders view.binders.getArgs fun params => do
        let (type, _) ← Term.withAutoBoundImplicit do
          let typeStx ← view.type?.getDM `(Sort _)
          let type ← Term.elabType typeStx
          Term.synthesizeSyntheticMVarsNoPostponing
          let inlayHintPos? := view.binders.getTailPos? (canonicalOnly := true)
            <|> view.declId.getTailPos? (canonicalOnly := true)
          let indices ← Term.addAutoBoundImplicits #[] inlayHintPos?
          let type ← mkForallFVars indices type
          if view.allowIndices then
            unless (← isTypeFormerType type) do
              throwErrorAt typeStx "invalid resulting type, expecting 'Sort _' or an indexed family of sorts"
          else
            unless (← whnfD type).isSort do
              throwErrorAt typeStx "invalid resulting type, expecting 'Type _' or 'Prop'"
          return (type, indices.size)
        let params ← Term.addAutoBoundImplicits params (view.declId.getTailPos? (canonicalOnly := true))
        trace[Elab.inductive] "header params: {params}, type: {type}"
        let levelNames ← Term.getLevelNames
        return acc.push { lctx := (← getLCtx), localInsts := (← getLocalInstances), levelNames, params, type, view }
      elabHeadersAux views (i+1) acc
    else
      return acc

/--
Elaborates all the headers in the inductive views.
-/
private def elabHeaders (views : Array InductiveView) : TermElabM (Array PreElabHeaderResult) := do
  let rs ← elabHeadersAux views 0 #[]
  if rs.size > 1 then
    checkUnsafe rs
    checkClass rs
    let numParams ← checkNumParams rs
    checkHeaders rs numParams 0 none
  return rs

/--
Create a local declaration for each inductive type in `rs`, and execute `x params indFVars`, where `params` are the inductive type parameters and
`indFVars` are the new local declarations.
We use the local context/instances and parameters of rs[0].
Note that this method is executed after we executed `checkHeaders` and established all
parameters are compatible.
-/
private def withInductiveLocalDecls (rs : Array PreElabHeaderResult) (x : Array Expr → Array Expr → TermElabM α) : TermElabM α := do
  let namesAndTypes ← rs.mapM fun r => do
    let type ← mkTypeFor r
    pure (r.view.declName, r.view.shortDeclName, type)
  let r0     := rs[0]!
  let params := r0.params
  withLCtx r0.lctx r0.localInsts <| withRef r0.view.ref do
    let rec loop (i : Nat) (indFVars : Array Expr) := do
      if h : i < namesAndTypes.size then
        let (declName, shortDeclName, type) := namesAndTypes[i]
        withAuxDecl shortDeclName type declName fun indFVar => loop (i+1) (indFVars.push indFVar)
      else
        x params indFVars
    loop 0 #[]

private def InductiveElabStep1.checkLevelNames (views : Array InductiveView) : TermElabM Unit := do
  if h : views.size > 1 then
    let levelNames := views[0].levelNames
    for view in views do
      unless view.levelNames == levelNames do
        throwErrorAt view.ref "invalid inductive type, universe parameters mismatch in mutually inductive datatypes"

private def ElabHeaderResult.checkLevelNames (rs : Array PreElabHeaderResult) : TermElabM Unit := do
  if h : rs.size > 1 then
    let levelNames := rs[0].levelNames
    for r in rs do
      unless r.levelNames == levelNames do
        throwErrorAt r.view.ref "invalid inductive type, universe parameters mismatch in mutually inductive datatypes"

/--
We need to work inside a single local context across all the inductive types, so we need to update the `ElabHeaderResult`s
so that resultant types refer to the fvars in `params`, the parameters for `rs[0]!` specifically.
Also updates the local contexts and local instances in each header.
-/
private def updateElabHeaderTypes (params : Array Expr) (rs : Array PreElabHeaderResult) (indFVars : Array Expr) : TermElabM (Array ElabHeaderResult) := do
  rs.mapIdxM fun i r => do
    /-
    At this point, because of `withInductiveLocalDecls`, the only fvars that are in context are the ones related to the first inductive type.
    Because of this, we need to replace the fvars present in each inductive type's header of the mutual block with those of the first inductive.
    However, some mvars may still be uninstantiated there, and might hide some of the old fvars.
    As such we first need to synthesize all possible mvars at this stage, instantiate them in the header types and only
    then replace the parameters' fvars in the header type.

    See issue #3242 (`https://github.com/leanprover/lean4/issues/3242`)
    -/
    let type ← instantiateMVars r.type
    let type := type.replaceFVars r.params params
    pure { r with lctx := ← getLCtx, localInsts := ← getLocalInstances, type := type, indFVar := indFVars[i]! }

private def getArity (indType : InductiveType) : MetaM Nat :=
  forallTelescopeReducing indType.type fun xs _ => return xs.size

private def resetMaskAt (mask : Array Bool) (i : Nat) : Array Bool :=
  mask.setIfInBounds i false

/--
Compute a bit-mask that for `indType`. The size of the resulting array `result` is the arity of `indType`.
The first `numParams` elements are `false` since they are parameters.
For `i ∈ [numParams, arity)`, we have that `result[i]` if this index of the inductive family is fixed.
-/
private def computeFixedIndexBitMask (numParams : Nat) (indType : InductiveType) (indFVars : Array Expr) : MetaM (Array Bool) := do
  let arity ← getArity indType
  if arity ≤ numParams then
    return mkArray arity false
  else
    let maskRef ← IO.mkRef (mkArray numParams false ++ mkArray (arity - numParams) true)
    let rec go (ctors : List Constructor) : MetaM (Array Bool) := do
      match ctors with
      | [] => maskRef.get
      | ctor :: ctors =>
        forallTelescopeReducing ctor.type fun xs type => do
          let typeArgs := type.getAppArgs
          for i in [numParams:arity] do
            unless i < xs.size && xs[i]! == typeArgs[i]! do -- Remark: if we want to allow arguments to be rearranged, this test should be xs.contains typeArgs[i]
              maskRef.modify fun mask => mask.set! i false
          for x in xs[numParams:] do
            let xType ← inferType x
            let cond (e : Expr) := indFVars.any (fun indFVar => e.getAppFn == indFVar)
            xType.forEachWhere (stopWhenVisited := true) cond fun e => do
              let eArgs := e.getAppArgs
              for i in [numParams:eArgs.size] do
                if i >= typeArgs.size then
                  maskRef.modify (resetMaskAt · i)
                else
                  unless eArgs[i]! == typeArgs[i]! do
                    maskRef.modify (resetMaskAt · i)
              /-If an index is missing in the arguments of the inductive type, then it must be non-fixed.
                Consider the following example:
                ```lean
                inductive All {I : Type u} (P : I → Type v) : List I → Type (max u v) where
                  | cons : P x → All P xs → All P (x :: xs)

                inductive Iμ {I : Type u}  : I → Type (max u v) where
                  | mk : (i : I)  → All Iμ [] → Iμ i
                ```
                because `i` doesn't appear in `All Iμ []`, the index shouldn't be fixed.
              -/
              for i in [eArgs.size:arity] do
                maskRef.modify (resetMaskAt · i)
        go ctors
    go indType.ctors

/-- Return true iff `arrowType` is an arrow and its domain is defeq to `type` -/
private def isDomainDefEq (arrowType : Expr) (type : Expr) : MetaM Bool := do
  if !arrowType.isForall then
    return false
  else
    /-
      We used to use `withNewMCtxDepth` to make sure we do not assign universe metavariables,
      but it was not satisfactory. For example, in declarations such as
      ```
      inductive Eq : α → α → Prop where
      | refl (a : α) : Eq a a
      ```
      We want the first two indices to be promoted to parameters, and this will only
      happen if we can assign universe metavariables.
    -/
    isDefEq arrowType.bindingDomain! type

/--
Convert fixed indices to parameters.
-/
private def fixedIndicesToParams (numParams : Nat) (indTypes : Array InductiveType) (indFVars : Array Expr) : MetaM Nat := do
  if !inductive.autoPromoteIndices.get (← getOptions) then
    return numParams
  let masks ← indTypes.mapM (computeFixedIndexBitMask numParams · indFVars)
  trace[Elab.inductive] "masks: {masks}"
  if masks.all fun mask => !mask.contains true then
    return numParams
  -- We process just a non-fixed prefix of the indices for now. Reason: we don't want to change the order.
  -- TODO: extend it in the future. For example, it should be reasonable to change
  -- the order of indices generated by the auto implicit feature.
  let mask := masks[0]!
  forallBoundedTelescope indTypes[0]!.type numParams fun params type => do
    let otherTypes ← indTypes[1:].toArray.mapM fun indType => do whnfD (← instantiateForall indType.type params)
    let ctorTypes ← indTypes.toList.mapM fun indType => indType.ctors.mapM fun ctor => do whnfD (← instantiateForall ctor.type params)
    let typesToCheck := otherTypes.toList ++ ctorTypes.flatten
    let rec go (i : Nat) (type : Expr) (typesToCheck : List Expr) : MetaM Nat := do
      if i < mask.size then
        if !masks.all fun mask => i < mask.size && mask[i]! then
           return i
        if !type.isForall then
          return i
        let paramType := type.bindingDomain!
        if !(← typesToCheck.allM fun type => isDomainDefEq type paramType) then
          trace[Elab.inductive] "domain not def eq: {i}, {type} =?= {paramType}"
          return i
        withLocalDeclD `a paramType fun paramNew => do
          let typesToCheck ← typesToCheck.mapM fun type => whnfD (type.bindingBody!.instantiate1 paramNew)
          go (i+1) (type.bindingBody!.instantiate1 paramNew) typesToCheck
      else
        return i
    go numParams type typesToCheck

private def getResultingUniverse : List InductiveType → TermElabM Level
  | []           => throwError "unexpected empty inductive declaration"
  | indType :: _ => forallTelescopeReducing indType.type fun _ r => do
    let r ← whnfD r
    match r with
    | Expr.sort u => return u
    | _           => throwError "unexpected inductive type resulting type{indentExpr r}"

/--
Returns `some ?m` if `u` is of the form `?m + k`.
Returns none if `u` does not contain universe metavariables.
Throw exception otherwise.
-/
def shouldInferResultUniverse (u : Level) : TermElabM (Option LMVarId) := do
  let u ← instantiateLevelMVars u
  if u.hasMVar then
    match u.getLevelOffset with
    | Level.mvar mvarId => return some mvarId
    | _ =>
      throwError "
        cannot infer resulting universe level of inductive datatype, \
        given resulting type contains metavariables{indentExpr <| mkSort u}\n\
        provide universe explicitly"
  else
    return none

/--
Converts universe metavariables into new parameters. It skips `univToInfer?` (the inductive datatype resulting universe) because
it should be inferred later using `inferResultingUniverse`.
-/
private def levelMVarToParam (indTypes : List InductiveType) (univToInfer? : Option LMVarId) : TermElabM (List InductiveType) :=
  indTypes.mapM fun indType => do
    let type  ← levelMVarToParam' indType.type
    let ctors ← indType.ctors.mapM fun ctor => do
      let ctorType ← levelMVarToParam' ctor.type
      return { ctor with type := ctorType }
    return { indType with ctors, type }
where
  levelMVarToParam' (type : Expr) : TermElabM Expr := do
    Term.levelMVarToParam type (except := fun mvarId => univToInfer? == some mvarId)

private structure AccLevelState where
  levels : Array Level := #[]
  /-- When we encounter `u ≤ ?r + k` with `k > 0`, we add `(u, k)` to the "bad levels".
  We use this to compute what the universe "should" have been. -/
  badLevels : Array (Level × Nat) := #[]

private def AccLevelState.push (acc : AccLevelState) (u : Level) (offset : Nat) : AccLevelState :=
  if offset == 0 then
    { acc with levels := if acc.levels.contains u then acc.levels else acc.levels.push u }
  else
    let p := (u, offset)
    { acc with badLevels := if acc.badLevels.contains p then acc.badLevels else acc.badLevels.push p }

/--
Auxiliary function for `updateResultingUniverse`.
Consider the constraint `u ≤ ?r + rOffset` where `u` has no metavariables except for perhaps `?r`.
This function attempts to find a unique minimal solution of the form `?r := max l₁ ... lₙ` where each `lᵢ` is normalized and not a `max`/`imax`.

It also records information about how "too big" `rOffset` is. Consider `u ≤ ?r + 1`, from for example
```lean
inductive I (α : Sort u) : Type _ where
  | mk (x : α)
```
This is likely a mistake. The correct solution would be `Type (max u 1)` rather than `Type (u + 1)`,
but by this point it is impossible to rectify. So, for `u ≤ ?r + 1` we record the pair of `u` and `1`
so that we can inform the user what they should have probably used instead.
-/
def accLevel (u : Level) (r : Level) (rOffset : Nat) : ExceptT MessageData (StateT AccLevelState Id) Unit := do
  go u rOffset
where
  go (u : Level) (rOffset : Nat) : ExceptT MessageData (StateT AccLevelState Id) Unit := do
    match u, rOffset with
    | .max u v,  rOffset   => go u rOffset; go v rOffset
    | .imax u v, rOffset   => go u rOffset; go v rOffset
    | .zero,     _         => return ()
    | .succ u,   rOffset+1 => go u rOffset
    | u,         rOffset   =>
      if u == r && rOffset == 0 then
        pure ()
      else if r.occurs u then
        /- `f(?r) = ?r + k`. -/
        throw m!"in the constraint {u} ≤ {Level.addOffset r rOffset}, the level metavariable {r} appears in both sides"
      else
        modify fun acc => acc.push u rOffset

/--
Auxiliary function for `updateResultingUniverse`. Applies `accLevel` to the given constructor parameter.
-/
def accLevelAtCtor (ctorParam : Expr) (r : Level) (rOffset : Nat) : StateT AccLevelState TermElabM Unit := do
  let type ← inferType ctorParam
  let u ← instantiateLevelMVars (← getLevel type)
  match (← modifyGet fun s => accLevel u r rOffset |>.run |>.run s) with
  | .ok _ => pure ()
  | .error msg =>
    throwError "failed to infer universe level for resulting type due to the constructor argument '{ctorParam}', {msg}"

/--
Executes `k` using the `Syntax` reference associated with constructor `ctorName`.
-/
def withCtorRef [Monad m] [MonadRef m] (views : Array InductiveView) (ctorName : Name) (k : m α) : m α := do
  for view in views do
    for ctor in view.ctors do
      if ctor.declName == ctorName then
        return (← withRef ctor.ref k)
  k

/-- Runs `k` with the resulting type as the ref or, if that's not available, with the view's ref. -/
def InductiveView.withTypeRef [Monad m] [MonadRef m] (view : InductiveView) (k : m α) : m α := do
  withRef view.ref do
    match view.type? with
    | some type => withRef type k
    | none      => k

def withViewTypeRef [Monad m] [MonadRef m] (views : Array InductiveView) (k : m α) : m α := do
  for view in views do
    if let some type := view.type? then
      return (← withRef type k)
  withRef views[0]!.ref k

/--
Auxiliary function for `updateResultingUniverse`. Computes a list of levels `l₁ ... lₙ` such that `r := max l₁ ... lₙ` can be a solution to the constraint problem.
-/
private def collectUniverses (views : Array InductiveView) (r : Level) (rOffset : Nat) (numParams : Nat) (indTypes : List InductiveType) : TermElabM (Array Level) := do
  let (_, acc) ← go |>.run {}
  if !acc.badLevels.isEmpty then
    withViewTypeRef views do
      let goodPart := Level.addOffset (Level.mkNaryMax acc.levels.toList) rOffset
      let badPart := Level.mkNaryMax (acc.badLevels.toList.map fun (u, k) => Level.max (Level.ofNat rOffset) (Level.addOffset u (rOffset - k)))
      let inferred := (Level.max goodPart badPart).normalize
      let badConstraints := acc.badLevels.map fun (u, k) => indentD m!"{u} ≤ {Level.addOffset r k}"
      throwError "resulting type is of the form{indentD <| mkSort (Level.addOffset r rOffset)}\n\
        but the universes of constructor arguments suggest that this could accidentally be a higher universe than necessary. \
        Explicitly providing a resulting type will silence this error. \
        Universe inference suggests using{indentD <| mkSort inferred}\n\
        if the resulting universe level should be at the above universe level or higher.\n\n\
        Explanation: At this point in elaboration, universe level unification has committed to using a \
        resulting universe level of the form '{Level.addOffset r rOffset}'. \
        Constructor argument universe levels must be no greater than the resulting universe level, and this condition implies the following constraint(s):\
        {MessageData.joinSep badConstraints.toList ""}\n\
        However, such constraint(s) usually indicate that the resulting universe level should have been in a different form. \
        For example, if the resulting type is of the form 'Sort (_ + 1)' and a constructor argument is in universe `Sort u`, \
        then universe inference would yield `Sort (u + 1)`, \
        but the resulting type `Sort (max 1 u)` would avoid being in a higher universe than necessary."
  return acc.levels
where
  go : StateT AccLevelState TermElabM Unit :=
    indTypes.forM fun indType => indType.ctors.forM fun ctor =>
      withCtorRef views ctor.name do
        forallTelescopeReducing ctor.type fun ctorParams _ =>
          for ctorParam in ctorParams[numParams:] do
            accLevelAtCtor ctorParam r rOffset

/--
Decides whether the inductive type should be `Prop`-valued when the universe is not given
and when the universe inference algorithm `collectUniverses` determines
that the inductive type could naturally be `Prop`-valued.
Recall: the natural universe level is the mimimum universe level for all the types of all the constructor parameters.

Heuristic:
- We want `Prop` when each inductive type is a syntactic subsingleton.
  That's to say, when each inductive type has at most one constructor.
  Such types carry no data anyway.
- Exception: if no inductive type has any constructors, these are likely stubbed-out declarations,
  so we prefer `Type` instead.
- Exception: if each constructor has no parameters, then these are likely partially-written enumerations,
  so we prefer `Type` instead.

Specialized to structures, the heuristic is that we prefer a `Prop` instead of a `Type` structure
when it could be a syntactic subsingleton.
Exception: no-field structures are `Type` since they are likely stubbed-out declarations.
-/
private def isPropCandidate (numParams : Nat) (indTypes : List InductiveType) : MetaM Bool := do
  unless indTypes.foldl (fun n indType => max n indType.ctors.length) 0 == 1 do
    return false
  for indType in indTypes do
    for ctor in indType.ctors do
      let cparams ← forallTelescopeReducing ctor.type fun ctorParams _ => pure (ctorParams.size - numParams)
      unless cparams == 0 do
        return true
  return false

private def mkResultUniverse (us : Array Level) (rOffset : Nat) (preferProp : Bool) : Level :=
  if us.isEmpty && rOffset == 0 then
    if preferProp then levelZero else levelOne
  else
    let r := Level.mkNaryMax us.toList
    if rOffset == 0 && !r.isZero && !r.isNeverZero then
      mkLevelMax r levelOne |>.normalize
    else
      r.normalize

/--
Given that the resulting type is of the form `Sort (?r + k)` with `?r` a metavariable,
try to infer the unique `?r` such that `?r + k` is the supremum of the constructor arguments' universe levels, if one exists.

Usually, we also throw in the constraint that `1 ≤ ?r + k`, but if `isPropCandidate` is true we allow the solution `?r + k = 0`.
-/
private def updateResultingUniverse (views : Array InductiveView) (numParams : Nat) (indTypes : List InductiveType) : TermElabM (List InductiveType) := do
  let r₀ ← getResultingUniverse indTypes
  let rOffset : Nat   := r₀.getOffset
  let r       : Level := r₀.getLevelOffset
  unless r.isMVar do
    throwError "failed to compute resulting universe level of inductive datatype, provide universe explicitly: {r₀}"
  let us ← collectUniverses views r rOffset numParams indTypes
  trace[Elab.inductive] "updateResultingUniverse us: {us}, r: {r}, rOffset: {rOffset}"
  let rNew := mkResultUniverse us rOffset (← isPropCandidate numParams indTypes)
  assignLevelMVar r.mvarId! rNew
  indTypes.mapM fun indType => do
    let type ← instantiateMVars indType.type
    let ctors ← indType.ctors.mapM fun ctor => return { ctor with type := (← instantiateMVars ctor.type) }
    return { indType with type, ctors }

/--
Heuristic: users don't tend to want types that are universe polymorphic across both `Prop` and `Type _`.
This can be disabled by setting the option `bootstrap.inductiveCheckResultingUniverse` to false,
unless one of the inductive commands requires it (for instance `structure` due to projections).
-/
private def checkResultingUniversePolymorphism (views : Array InductiveView) (u : Level) (_numParams : Nat) (_indTypes : List InductiveType) : TermElabM Unit := do
  let doErrFor := fun view =>
    view.withTypeRef do
      throwError "\
        invalid universe polymorphic resulting type, the resulting universe is not 'Prop', but it may be 'Prop' for some parameter values:{indentD (mkSort u)}\n\
        Possible solution: use levels of the form 'max 1 _' or '_ + 1' to ensure the universe is of the form 'Type _'."
  unless u.isZero || u.isNeverZero do
    for view in views do
      if !view.allowSortPolymorphism then
        doErrFor view
    if bootstrap.inductiveCheckResultingUniverse.get (← getOptions) then
      -- TODO: heuristic for allowing `Sort` polymorphism?
      doErrFor views[0]!

/--
Solves for level metavariables in constructor argument types that are completely determined by the resulting type.
-/
private partial def propagateUniversesToConstructors (numParams : Nat) (indTypes : List InductiveType) : TermElabM Unit := do
  let u := (← instantiateLevelMVars (← getResultingUniverse indTypes)).normalize
  unless u.isZero do
    let r := u.getLevelOffset
    let k := u.getOffset
    indTypes.forM fun indType => indType.ctors.forM fun ctor =>
      forallTelescopeReducing ctor.type fun ctorArgs _ => do
        for ctorArg in ctorArgs[numParams:] do
          let type ← inferType ctorArg
          let v := (← instantiateLevelMVars (← getLevel type)).normalize
          if v.hasMVar then
            if r matches .param .. | .zero then
              discard <| observing? <| propagateConstraint v r k
where
  /--
  Solves for metavariables in `v` that are fully determined by the constraint `v ≤ r + k`,
  *assuming that `v` is either a parameter or zero* and assuming that `v` is normalized.
  Fails if we detect the constraint cannot be satisfied, letting the caller backtrack the assignments.

  If `r` isn't a parameter or zero, then there is nothing we can say.
  For example, `v ≤ max a b` could be satisfied by either constraint `v ≤ a` or `v ≤ b`.
  We do not need to handle the case where `r` is a metavariable, which is instead `updateResultingUniverse`.
  -/
  propagateConstraint (v : Level) (r : Level) (k : Nat) : MetaM Unit := do
    match v, k with
    | .zero,     _   => pure ()
    | .succ _,   0   => throwError "(for debug) {v} ≤ 0 is impossible"
    | .succ u,   k+1 => propagateConstraint u r k
    | .max u v,  k   => propagateConstraint u r k; propagateConstraint v r k
    /-
    Given `imax u v ≤ r + k`, then certainly `v ≤ r + k`.
    If this then implies `v` is never zero, then we can also impose `u ≤ r + k`,
    however, this never happens since the metavariable assignments are all of the form `?m := p` or `?m := 0`,
    and so `v` cannot become never zero.
    -/
    | .imax _ v, k   => propagateConstraint v r k
    /-
    `p ≤ r + k` is satisfied iff `r` is also a parameter and it is equal to `p`.
    -/
    | .param _,  _   => guard <| v == r
    /-
    `?v ≤ r + k` is uniquely solved iff `k = 0`, since otherwise there are solutions `?v := r`, `?v := r + 1`, ... `?v := r + (k - 1)`.
    -/
    | .mvar id,  k   =>
      if let some v' ← getLevelMVarAssignment? id then
        propagateConstraint v'.normalize r k
      else if k == 0 then
        /- Constrained, so assign. -/
        assignLevelMVar id r
      else
        /- Underconstrained, but not an error. -/
        pure ()

/-- Checks the universe constraints for each constructor. -/
private def checkResultingUniverses (views : Array InductiveView) (elabs' : Array InductiveElabStep2)
    (numParams : Nat) (indTypes : List InductiveType) : TermElabM Unit := do
  let u := (← instantiateLevelMVars (← getResultingUniverse indTypes)).normalize
  checkResultingUniversePolymorphism views u numParams indTypes
  unless u.isZero do
    for h : i in [0:indTypes.length] do
      let indType := indTypes[i]
      -- See if there is a custom error. If so, this should throw an error first:
      elabs'[i]!.checkUniverses numParams u
      indType.ctors.forM fun ctor =>
      forallTelescopeReducing ctor.type fun ctorArgs _ => do
        for ctorArg in ctorArgs[numParams:] do
          let type ← inferType ctorArg
          let v := (← instantiateLevelMVars (← getLevel type)).normalize
          unless u.geq v do
            let mut msg := m!"invalid universe level in constructor '{ctor.name}', parameter"
            unless (← ctorArg.fvarId!.getUserName).hasMacroScopes do
              msg := msg ++ m!" '{ctorArg}'"
            msg := msg ++ m!" has type{indentExpr type}\n\
              at universe level{indentD v}\n\
              which is not less than or equal to the inductive type's resulting universe level{indentD u}"
            withCtorRef views ctor.name <| throwError msg

private def collectUsed (indTypes : List InductiveType) : StateRefT CollectFVars.State MetaM Unit := do
  indTypes.forM fun indType => do
    indType.type.collectFVars
    indType.ctors.forM fun ctor =>
      ctor.type.collectFVars

private def removeUnused (elabs : Array InductiveElabStep2) (vars : Array Expr) (indTypes : List InductiveType) : TermElabM (LocalContext × LocalInstances × Array Expr) := do
  let (_, used) ← (collectUsed indTypes *> elabs.forM fun e => e.collectUsedFVars).run {}
  Meta.removeUnused vars used

private def withUsed {α} (elabs : Array InductiveElabStep2) (vars : Array Expr) (indTypes : List InductiveType) (k : Array Expr → TermElabM α) : TermElabM α := do
  let (lctx, localInsts, vars) ← removeUnused elabs vars indTypes
  withLCtx lctx localInsts <| k vars

private def updateParams (vars : Array Expr) (indTypes : List InductiveType) : TermElabM (List InductiveType) :=
  indTypes.mapM fun indType => do
    let type ← mkForallFVars vars indType.type
    let ctors ← indType.ctors.mapM fun ctor => do
      let ctorType ← withExplicitToImplicit vars (mkForallFVars vars ctor.type)
      return { ctor with type := ctorType }
    return { indType with type, ctors }

private def collectLevelParamsInInductive (indTypes : List InductiveType) : Array Name := Id.run do
  let mut usedParams : CollectLevelParams.State := {}
  for indType in indTypes do
    usedParams := collectLevelParams usedParams indType.type
    for ctor in indType.ctors do
      usedParams := collectLevelParams usedParams ctor.type
  return usedParams.params

private def mkIndFVar2Const (views : Array InductiveView) (indFVars : Array Expr) (levelNames : List Name) : ExprMap Expr := Id.run do
  let levelParams := levelNames.map mkLevelParam;
  let mut m : ExprMap Expr := {}
  for h : i in [:views.size] do
    let view    := views[i]
    let indFVar := indFVars[i]!
    m := m.insert indFVar (mkConst view.declName levelParams)
  return m

/-- Remark: `numVars <= numParams`. `numVars` is the number of context `variables` used in the inductive declaration,
   and `numParams` is `numVars` + number of explicit parameters provided in the declaration. -/
private def replaceIndFVarsWithConsts (views : Array InductiveView) (indFVars : Array Expr) (levelNames : List Name)
    (numVars : Nat) (numParams : Nat) (indTypes : List InductiveType) : TermElabM (List InductiveType) :=
  let indFVar2Const := mkIndFVar2Const views indFVars levelNames
  indTypes.mapM fun indType => do
    let ctors ← indType.ctors.mapM fun ctor => do
      let type ← forallBoundedTelescope ctor.type numParams fun params type => do
        let type := type.replace fun e =>
          if !e.isFVar then
            none
          else match indFVar2Const[e]? with
            | none   => none
            | some c => mkAppN c (params.extract 0 numVars)
        instantiateMVars (← mkForallFVars params type)
      return { ctor with type }
    return { indType with ctors }

private structure FinalizeContext where
  elabs : Array InductiveElabStep2
  mctx : MetavarContext
  levelParams : List Name
  params : Array Expr
  lctx : LocalContext
  localInsts : LocalInstances
  replaceIndFVars : Expr → MetaM Expr

private def mkInductiveDecl (vars : Array Expr) (elabs : Array InductiveElabStep1) : TermElabM FinalizeContext :=
  Term.withoutSavingRecAppSyntax do
  let views := elabs.map (·.view)
  let view0 := views[0]!
  let scopeLevelNames ← Term.getLevelNames
  InductiveElabStep1.checkLevelNames views
  let allUserLevelNames := view0.levelNames
  let isUnsafe          := view0.modifiers.isUnsafe
  withRef view0.ref <| Term.withLevelNames allUserLevelNames do
    let rs ← elabHeaders views
    Term.synthesizeSyntheticMVarsNoPostponing
    ElabHeaderResult.checkLevelNames rs
    let allUserLevelNames := rs[0]!.levelNames
    trace[Elab.inductive] "level names: {allUserLevelNames}"
    let res ← withInductiveLocalDecls rs fun params indFVars => do
      trace[Elab.inductive] "indFVars: {indFVars}"
      let rs ← updateElabHeaderTypes params rs indFVars
      let mut indTypesArray : Array InductiveType := #[]
      let mut elabs' := #[]
      for h : i in [:views.size] do
        Term.addLocalVarInfo views[i].declId indFVars[i]!
        let r     := rs[i]!
        let elab' ← elabs[i]!.elabCtors rs r params
        elabs'    := elabs'.push elab'
        let type  ← mkForallFVars params r.type
        indTypesArray := indTypesArray.push { name := r.view.declName, type, ctors := elab'.ctors }
      Term.synthesizeSyntheticMVarsNoPostponing
      let numExplicitParams ← fixedIndicesToParams params.size indTypesArray indFVars
      trace[Elab.inductive] "numExplicitParams: {numExplicitParams}"
      let indTypes := indTypesArray.toList
      let u ← getResultingUniverse indTypes
      let univToInfer? ← shouldInferResultUniverse u
      withUsed elabs' vars indTypes fun vars => do
        let numVars   := vars.size
        let numParams := numVars + numExplicitParams
        let indTypes ← updateParams vars indTypes
        let indTypes ←
          if let some univToInfer := univToInfer? then
            updateResultingUniverse views numParams (← levelMVarToParam indTypes univToInfer)
          else
            propagateUniversesToConstructors numParams indTypes
            levelMVarToParam indTypes none
        checkResultingUniverses views elabs' numParams indTypes
        elabs'.forM fun elab' => elab'.finalizeTermElab
        let usedLevelNames := collectLevelParamsInInductive indTypes
        match sortDeclLevelParams scopeLevelNames allUserLevelNames usedLevelNames with
        | .error msg      => throwErrorAt view0.declId msg
        | .ok levelParams => do
          let indTypes ← replaceIndFVarsWithConsts views indFVars levelParams numVars numParams indTypes
          let decl := Declaration.inductDecl levelParams numParams indTypes isUnsafe
          Term.ensureNoUnassignedMVars decl
          addDecl decl

          -- For nested inductive types, the kernel adds a variable number of auxiliary recursors.
          -- Let the elaborator know about them as well. (Other auxiliaries have already been
          -- registered by `addDecl` via `Declaration.getNames`.)
          -- NOTE: If we want to make inductive elaboration parallel, this should switch to using
          -- reserved names.
          for indType in indTypes do
            let mut i := 1
            while true do
              let auxRecName := indType.name ++ `rec |>.appendIndexAfter i
              let env ← getEnv
              let some const := env.toKernelEnv.find? auxRecName | break
              let res ← env.addConstAsync auxRecName .recursor
              res.commitConst res.asyncEnv (info? := const)
              res.commitCheckEnv res.asyncEnv
              setEnv res.mainEnv
              i := i + 1

          let replaceIndFVars (e : Expr) : MetaM Expr := do
            let indFVar2Const := mkIndFVar2Const views indFVars levelParams
            return (← instantiateMVars e).replace fun e' =>
              if !e'.isFVar then
                none
              else
                match indFVar2Const[e']? with
                | none   => none
                | some c => mkAppN c vars
          -- Now the indFVars are (mostly) unnecessary, so rename them to prevent shadowing in messages.
          -- Inductive elaborators might still have some indFVars around, but they should use `replaceIndFVars` as soon as possible during their `finalize` procedure.
          let lctx := rs.foldl (init := ← getLCtx) (fun lctx r => lctx.modifyLocalDecl r.indFVar.fvarId! fun decl => decl.setUserName (`_indFVar ++ decl.userName))
          pure {
            elabs := elabs', levelParams, params := vars ++ params, replaceIndFVars,
            mctx := ← getMCtx, lctx, localInsts := ← getLocalInstances }
    withSaveInfoContext do -- save new env
      for view in views do
        Term.addTermInfo' view.declId (← mkConstWithLevelParams view.declName) (isBinder := true)
        for ctor in view.ctors do
          if (ctor.declId.getPos? (canonicalOnly := true)).isSome then
            Term.addTermInfo' ctor.declId (← mkConstWithLevelParams ctor.declName) (isBinder := true)
            enableRealizationsForConst ctor.declName
    return res

private def mkAuxConstructions (declNames : Array Name) : TermElabM Unit := do
  let env ← getEnv
  let hasEq   := env.contains ``Eq
  let hasHEq  := env.contains ``HEq
  let hasUnit := env.contains ``PUnit
  let hasProd := env.contains ``Prod
  for n in declNames do
    mkRecOn n
    if hasUnit then mkCasesOn n
    if hasUnit && hasEq && hasHEq then mkNoConfusion n
    if hasUnit && hasProd then mkBelow n
    if hasUnit && hasProd then mkIBelow n
  for n in declNames do
    if hasUnit && hasProd then mkBRecOn n
    if hasUnit && hasProd then mkBInductionOn n

private def elabInductiveViews (vars : Array Expr) (elabs : Array InductiveElabStep1) : TermElabM FinalizeContext := do
  let view0 := elabs[0]!.view
  let ref := view0.ref
  Term.withDeclName view0.declName do withRef ref do
    let res ← mkInductiveDecl vars elabs
    mkAuxConstructions (elabs.map (·.view.declName))
    unless view0.isClass do
      mkSizeOfInstances view0.declName
      IndPredBelow.mkBelow view0.declName
      for e in elabs do
        mkInjectiveTheorems e.view.declName
    for e in elabs do
      enableRealizationsForConst e.view.declName
    return res

/-- Ensures that there are no conflicts among or between the type and constructor names defined in `elabs`. -/
private def checkNoInductiveNameConflicts (elabs : Array InductiveElabStep1) : TermElabM Unit := do
  let throwErrorsAt (init cur : Syntax) (msg : MessageData) : TermElabM Unit := do
    logErrorAt init msg
    throwErrorAt cur msg
  -- Maps names of inductive types to to `true` and those of constructors to `false`, along with syntax refs
  let mut uniqueNames : Std.HashMap Name (Bool × Syntax) := {}
  for { view, .. } in elabs do
    let typeDeclName := privateToUserName view.declName
    if let some (prevNameIsType, prevRef) := uniqueNames[typeDeclName]? then
      let declKinds := if prevNameIsType then "multiple inductive types" else "an inductive type and a constructor"
      throwErrorsAt prevRef view.declId m!"cannot define {declKinds} with the same name '{typeDeclName}'"
    uniqueNames := uniqueNames.insert typeDeclName (true, view.declId)
    for ctor in view.ctors do
      let ctorName := privateToUserName ctor.declName
      if let some (prevNameIsType, prevRef) := uniqueNames[ctorName]? then
        let declKinds := if prevNameIsType then "an inductive type and a constructor" else "multiple constructors"
        throwErrorsAt prevRef ctor.declId m!"cannot define {declKinds} with the same name '{ctorName}'"
      uniqueNames := uniqueNames.insert ctorName (false, ctor.declId)

private def applyComputedFields (indViews : Array InductiveView) : CommandElabM Unit := do
  if indViews.all (·.computedFields.isEmpty) then return

  let mut computedFields := #[]
  let mut computedFieldDefs := #[]
  for indView@{declName, ..} in indViews do
    for {ref, fieldId, type, matchAlts, modifiers, ..} in indView.computedFields do
      computedFieldDefs := computedFieldDefs.push <| ← do
        let modifiers ← match modifiers with
          | `(Lean.Parser.Command.declModifiersT| $[$doc:docComment]? $[$attrs:attributes]? $[$vis]? $[noncomputable]?) =>
            `(Lean.Parser.Command.declModifiersT| $[$doc]? $[$attrs]? $[$vis]? noncomputable)
          | _ => do
            withRef modifiers do logError "unsupported modifiers for computed field"
            `(Parser.Command.declModifiersT| noncomputable)
        `($(⟨modifiers⟩):declModifiers
          def%$ref $(mkIdent <| `_root_ ++ declName ++ fieldId):ident : $type $matchAlts:matchAlts)
    let computedFieldNames := indView.computedFields.map fun {fieldId, ..} => declName ++ fieldId
    computedFields := computedFields.push (declName, computedFieldNames)
  withScope (fun scope => { scope with
      opts := scope.opts
        |>.setBool `bootstrap.genMatcherCode false
        |>.setBool `elaboratingComputedFields true}) <|
    elabCommand <| ← `(mutual $computedFieldDefs* end)

  liftTermElabM do Term.withDeclName indViews[0]!.declName do
    ComputedFields.setComputedFields computedFields

private def applyDerivingHandlers (views : Array InductiveView) : CommandElabM Unit := do
  let mut processed : NameSet := {}
  for view in views do
    for classView in view.derivingClasses do
      let className := classView.className
      unless processed.contains className do
        processed := processed.insert className
        let mut declNames := #[]
        for view in views do
          if view.derivingClasses.any fun classView => classView.className == className then
            declNames := declNames.push view.declName
        classView.applyHandlers declNames

private def elabInductiveViewsPostprocessing (views : Array InductiveView) (res : FinalizeContext) : CommandElabM Unit := do
  let view0 := views[0]!
  let ref := view0.ref
  applyComputedFields views -- NOTE: any generated code before this line is invalid
  liftTermElabM <| withMCtx res.mctx <| withLCtx res.lctx res.localInsts do
    for elab' in res.elabs do elab'.prefinalize res.levelParams res.params res.replaceIndFVars
    for view in views do withRef view.declId <| Term.applyAttributesAt view.declName view.modifiers.attrs .afterTypeChecking
    for elab' in res.elabs do elab'.finalize res.levelParams res.params res.replaceIndFVars
  applyDerivingHandlers views
  runTermElabM fun _ => Term.withDeclName view0.declName do withRef ref do
    for view in views do withRef view.declId <| Term.applyAttributesAt view.declName view.modifiers.attrs .afterCompilation

def elabInductives (inductives : Array (Modifiers × Syntax)) : CommandElabM Unit := do
  let (elabs, res) ← runTermElabM fun vars => do
    let elabs ← inductives.mapM fun (modifiers, stx) => mkInductiveView modifiers stx
    elabs.forM fun e => checkValidInductiveModifier e.view.modifiers
    checkNoInductiveNameConflicts elabs
    let res ← elabInductiveViews vars elabs
    pure (elabs, res)
  elabInductiveViewsPostprocessing (elabs.map (·.view)) res

def elabInductive (modifiers : Modifiers) (stx : Syntax) : CommandElabM Unit := do
  elabInductives #[(modifiers, stx)]

/--
Returns true if all elements of the `mutual` block (`Lean.Parser.Command.mutual`) are inductive declarations.
-/
def isMutualInductive [Monad m] [MonadEnv m] (stx : Syntax) : m Bool :=
  stx[1].getArgs.allM fun elem => isInductiveCommand elem[1]

/--
Elaborates a `mutual` block, assuming the commands satisfy `Lean.Elab.Command.isMutualInductive`.
-/
def elabMutualInductive (elems : Array Syntax) : CommandElabM Unit := do
  let inductives ← elems.mapM fun stx => do
    let modifiers ← elabModifiers ⟨stx[0]⟩
    pure (modifiers, stx[1])
  elabInductives inductives

end Lean.Elab.Command
