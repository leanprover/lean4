/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Kyle Miller
-/
module

prelude
public import Lean.Meta.Constructions
public import Lean.Meta.SizeOf
public import Lean.Meta.MkIffOfInductiveProp
public import Lean.Elab.Coinductive
public import Lean.Elab.Deriving.Basic
import Lean.Elab.ComputedFields
import Lean.Meta.Constructions.CtorIdx
import Lean.Meta.Constructions.CtorElim
import Lean.Meta.IndPredBelow
import Lean.Meta.Injective
import Init.Data.List.MapIdx
import Init.Omega

public section

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
  /-- The declaration docstring, and whether it's Verso -/
  docString?      : Option (TSyntax ``Lean.Parser.Command.docComment × Bool)
  isCoinductive : Bool := false
  deriving Inhabited

/-- Elaborated header for an inductive type before fvars for each inductive are added to the local context. -/
structure PreElabHeaderResult where
  view       : InductiveView
  levelNames : List Name
  numParams  : Nat
  type       : Expr
  /-- The parameters in the header's initial local context. Used for adding fvar alias terminfo. -/
  origParams : Array Expr
  deriving Inhabited

/-- The elaborated header with the `indFVar` registered for this inductive type. -/
structure ElabHeaderResult extends PreElabHeaderResult where
  indFVar    : Expr
  deriving Inhabited

/-- An intermediate step for mutual inductive elaboration. See `InductiveElabDescr` -/
structure InductiveElabStep3 where
  /-- Finalize the inductive type, after they are all added to the environment, after auxiliary definitions are added, and after computed fields are registered.
  The `levelParams`, `params`, and `replaceIndFVars` arguments of `prefinalize` are still valid here. -/
  finalize : TermElabM Unit := pure ()

/-- An intermediate step for mutual inductive elaboration. See `InductiveElabDescr`. -/
structure InductiveElabStep2 where
  /-- The constructors produced by `InductiveElabStep1`. -/
  ctors : List Constructor
  /-- Function to collect additional fvars that might be missed by the constructors.
  It is permissible to include fvars that do not exist in the local context (`structure` for example includes its field fvars). -/
  collectUsedFVars : StateRefT CollectFVars.State MetaM Unit := pure ()
  /-- Function to collect additional level metavariables that are header-like (e.g. in `extends` clauses in `structure`).
  Header-like level metavariables can be promoted to be level parameters. -/
  collectExtraHeaderLMVars : StateRefT CollectLevelMVars.State MetaM Unit := pure ()
  /-- Function to check universes and provide a custom error. (`structure` uses this to do checks per field to give nicer messages.) -/
  checkUniverses (numParams : Nat) (u : Level) : TermElabM Unit := pure ()
  /-- Step to do final term elaboration error reporting, done immediately after universe levels are fully elaborated, but before the final level checks. -/
  finalizeTermElab : TermElabM Unit := pure ()
  /-- Like `finalize`, but occurs before `afterTypeChecking` attributes. -/
  prefinalize (levelParams : List Name) (params : Array Expr) (replaceIndFVars : Expr → MetaM Expr) : TermElabM InductiveElabStep3 := fun _ _ _ => pure {}
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
- Universe levels are checked. Commands can give custom errors using `InductiveStep2.checkUniverses`.
- Elaboration of constructors is finalized, with additional tasks done by each `InductiveStep2.finalizeTermElab`.
- The inductive family is added to the environment and is checked by the kernel.
- Attributes and other finalization activities are performed, including those defined
  by `InductiveStep2.prefinalize` and `InductiveStep3.finalize`.
-/
structure InductiveElabDescr where
  mkInductiveView : Modifiers → Syntax → TermElabM InductiveElabStep1
  deriving Inhabited

/--
Registers an inductive type elaborator for the given syntax node kind.

Commands registered using this attribute are allowed to be used together in mutual blocks with
other inductive type commands. This attribute is mostly used internally for `inductive` and
`structure`.

An inductive type elaborator should have type `Lean.Elab.Command.InductiveElabDescr`.
-/
@[builtin_doc]
builtin_initialize inductiveElabAttr : KeyedDeclsAttribute InductiveElabDescr ←
  unsafe KeyedDeclsAttribute.init {
    builtinName := `builtin_inductive_elab,
    name := `inductive_elab,
    descr    := "Register an elaborator for inductive types",
    valueTypeName := ``InductiveElabDescr
  }

/--
Returns true if the syntax participates in the mutual inductive elaborator.
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
    throwErrorAt stx "Failed to elaborate inductive type declaration: There is no `@[inductive_elab]` \
      handler for `{.ofConstName stx.getKind}` syntax"
  handlers[0]!.mkInductiveView modifiers stx

def checkValidInductiveModifier [Monad m] [MonadError m] (modifiers : Modifiers) : m Unit := do
  if modifiers.isNoncomputable then
    throwError "Invalid modifier: Inductive declarations cannot be marked as `noncomputable`"
  if modifiers.isPartial then
    throwError "Invalid modifier: Inductive declarations cannot be marked as `partial`"

def checkValidCtorModifier [Monad m] [MonadError m] (modifiers : Modifiers) : m Unit := do
  if modifiers.isNoncomputable then
    throwError "Invalid modifier: Constructors cannot be marked as `noncomputable`"
  if modifiers.isPartial then
    throwError "Invalid modifier: Constructors cannot be marked as `partial`"
  if modifiers.isUnsafe then
    throwError "Invalid modifier: Constructors cannot be marked as `unsafe`"
  if modifiers.attrs.size != 0 then
    throwError "Invalid attribute: Attributes cannot be added to constructors"

private def checkUnsafe (rs : Array PreElabHeaderResult) : TermElabM Unit := do
  let isUnsafe := rs[0]!.view.modifiers.isUnsafe
  for r in rs do
    unless r.view.modifiers.isUnsafe == isUnsafe do
      let unsafeStr (b : Bool) := if b then "unsafe" else "safe"
      throwErrorAt r.view.ref m!"Invalid mutually inductive types: `{r.view.declName}` is {unsafeStr (!isUnsafe)}, \
        but `{rs[0]!.view.declName}` is {unsafeStr isUnsafe}"
        ++ .note m!"Safe and unsafe inductive declarations cannot both occur in the same `mutual` block"

private def checkClass (rs : Array PreElabHeaderResult) : TermElabM Unit := do
  if rs.size > 1 then
    for r in rs do
      if r.view.isClass then
        throwErrorAt r.view.ref "Invalid mutually inductive type: Mutually inductive classes are not supported"

private def checkNumParams (rs : Array PreElabHeaderResult) : TermElabM Nat := do
  let numParams := rs[0]!.numParams
  for r in rs do
    unless r.numParams == numParams do
      throwErrorAt r.view.ref m!"Invalid mutually inductive types: `{r.view.shortDeclName}` has {r.numParams} \
        parameter(s), but the preceding type `{rs[0]!.view.shortDeclName}` has {numParams}"
        ++ .note m!"All inductive types declared in the same `mutual` block must have the same parameters"
  return numParams

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
  withRef view.ref <| withRef? view.type? k

def withViewTypeRef [Monad m] [MonadRef m] (views : Array InductiveView) (k : m α) : m α := do
  for view in views do
    if let some type := view.type? then
      return (← withRef type k)
  withRef views[0]!.ref k

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
          throwError m!"The resulting type of this declaration{indentExpr type}\ndiffers from a preceding one{indentExpr firstType}"
            ++ .note "All inductive types declared in the same `mutual` block must belong to the same type universe"
      | _ =>
        throwError "The specified resulting type{inlineExpr type}is not a type"
  catch
    | Exception.error ref msg => throw (Exception.error ref m!"Invalid mutually inductive types: {msg}")
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
    let type := r.type
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
              throwErrorAt typeStx m!"Invalid resulting type: Expected a sort or an indexed family of sorts"
                ++ .hint' m!"Examples of valid sorts include `Type _`, `Sort _`, and `Prop`"
          else
            unless (← whnfD type).isSort do
              throwErrorAt typeStx m!"Invalid resulting type: Expected a sort"
                ++ .hint' m!"Examples of valid sorts include `Type _`, `Sort _`, and `Prop`"
          return (type, indices.size)
        let params ← Term.addAutoBoundImplicits params (view.declId.getTailPos? (canonicalOnly := true))
        trace[Elab.inductive] "header params: {params}, type: {type}"
        let levelNames ← Term.getLevelNames
        let type ← mkForallFVars params type
        return acc.push { levelNames, numParams := params.size, type, view, origParams := params }
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
We use the parameters of rs[0].
Note that this method is executed after we executed `checkHeaders` and established all
parameters are compatible.
-/
private def withInductiveLocalDecls (rs : Array PreElabHeaderResult) (x : Array Expr → Array Expr → TermElabM α) : TermElabM α := do
  let r0 := rs[0]!
  forallBoundedTelescope r0.type r0.numParams fun params _ => withRef r0.view.ref do
    let rec loop (i : Nat) (indFVars : Array Expr) := do
      if h : i < rs.size then
        let r := rs[i]
        for param in params, origParam in r.origParams do
          if let .fvar origFVar := origParam then
            Elab.pushInfoLeaf <| .ofFVarAliasInfo { id := param.fvarId!, baseId := origFVar, userName := ← param.fvarId!.getUserName }
        withAuxDecl r.view.shortDeclName r.type r.view.declName fun indFVar =>
          loop (i+1) (indFVars.push indFVar)
      else
        x params indFVars
    loop 0 #[]

private def throwLevelNameMismatch [Monad m] [MonadError m]
    (curNames prevNames : List Name) (curDeclName prevDeclName : Name) : m α :=
  let listNames (names : List Name) := MessageData.joinSep (names.map (m!"`{·}`")) ", "
  throwError m!"Universe parameter mismatch in mutually inductive types: `{curDeclName}` \
    has universe parameters{indentD (listNames curNames)}\nbut the preceding declaration \
    `{prevDeclName}` has{indentD (listNames prevNames)}"
    ++ .note m!"All inductive declarations in the same `mutual` block must have the same universe level parameters"

private def InductiveElabStep1.checkLevelNames (views : Array InductiveView) : TermElabM Unit := do
  if h : views.size > 1 then
    let levelNames := views[0].levelNames
    for view in views do
      unless view.levelNames == levelNames do
        withRef view.ref <| throwLevelNameMismatch view.levelNames levelNames view.shortDeclName views[0].shortDeclName

private def ElabHeaderResult.checkLevelNames (rs : Array PreElabHeaderResult) : TermElabM Unit := do
  if h : rs.size > 1 then
    let levelNames := rs[0].levelNames
    for r in rs do
      unless r.levelNames == levelNames do
        throwLevelNameMismatch r.levelNames levelNames r.view.declName rs[0].view.shortDeclName

private def getResultingUniverse : List InductiveType → TermElabM Level
  | []           => throwError "Unexpected empty inductive declaration"
  | indType :: _ => forallTelescopeReducing indType.type fun _ r => do
    let r ← whnfD r
    match r with
    | Expr.sort u => return u
    | _           => throwError "Unexpected inductive type resulting type{indentExpr r}"

private def instantiateMVarsAtInductive (indType : InductiveType) : TermElabM InductiveType := do
  let type ← instantiateMVars indType.type
  let ctors ← indType.ctors.mapM fun ctor => return { ctor with type := (← instantiateMVars ctor.type) }
  return { indType with type, ctors }

section IndexPromotion
/-!
## Index-to-parameter promotion

The basic convention for `inductive` is that the binders before the colon in a type former
correspond to the type parameters, and the pi types after the colon correspond to the indices.

Indices that are fixed across all occurrences of the type former can potentially be promoted
to be parameters instead. Motivations:
- The recursor is more efficient (though the induction principle might be more rigid than expected;
  this is solved by generalizing variables)
- The inferred universe level of the inductive type might decrease.

Recall that when an inductive type declaration `Declaration.inductDecl` is sent to the kernel,
every constructor is provided its full type, including the inductive parameters.
The `inductDecl` declaration itself specifies how many parameters there are (`nparams`),
and the first `nparams` parameters of a constructor are the parameters for the inductive type.

The function `fixedIndicesToParams` determines by how much `nparams` can be increased
without resulting in an invalid inductive type declaration.
We say the indices that become parameters this way are *promoted*.
Only a prefix of indices can be promoted because of this.

Note that it currently does not do any constructor parameter reordering.
If the parameter for an index does not appear in the correct position in a constructor for it to be
an inductive type parameter, it is not promoted.
That said, the `inductive` command itself has some capacity for reordering
in `Lean.Elab.Command.reorderCtorArgs`.

Promotion can be disabled with `set_option inductive.autoPromoteIndices false`.
-/

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
    return .replicate arity false
  else
    let maskRef ← IO.mkRef (.replicate numParams false ++ .replicate (arity - numParams) true)
    let rec go (ctors : List Constructor) : MetaM (Array Bool) := do
      match ctors with
      | [] => maskRef.get
      | ctor :: ctors =>
        forallTelescopeReducing ctor.type fun xs type => do
          let typeArgs := type.getAppArgs
          for i in numParams...arity do
            unless i < xs.size && xs[i]! == typeArgs[i]! do -- Remark: if we want to allow arguments to be rearranged, this test should be xs.contains typeArgs[i]
              maskRef.modify fun mask => mask.set! i false
          for x in xs[numParams...*] do
            let xType ← inferType x
            let cond (e : Expr) := indFVars.any (fun indFVar => e.getAppFn == indFVar)
            xType.forEachWhere (stopWhenVisited := true) cond fun e => do
              let eArgs := e.getAppArgs
              for i in numParams...eArgs.size do
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
              for i in eArgs.size...arity do
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
Promote fixed indices to parameters.

The requirement for promotion is relatively strict. Given a constructor
```
Iᵢ.ctor p₁ … pₙ f₁ … fₘ : I p₁ … pₙ f₁ … fⱼ e₁ … eₖ
```
then the first `j` indices are potentially eligible for promotion to parameters.
Additionally, the fields must be definitionally equal across all constructors to be eligible for promotion.
-/
private def fixedIndicesToParams (numParams : Nat) (indTypes : List InductiveType) (indFVars : Array Expr) : MetaM Nat := do
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
  forallBoundedTelescope indTypes.head!.type numParams fun params type => do
    let otherTypes ← indTypes.tail.mapM fun indType => do whnfD (← instantiateForall indType.type params)
    let ctorTypes ← indTypes.mapM fun indType => indType.ctors.mapM fun ctor => do whnfD (← instantiateForall ctor.type params)
    let typesToCheck := otherTypes ++ ctorTypes.flatten
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

end IndexPromotion


section LevelInference
/-!
## Level metavariable inference

Terminology: Given the inductive type former `I : ... -> Sort u`,
we call `Sort u` the *resulting universe* of `I` and `u` the *resulting universe level* of `I`.

After constructor elaboration, inductive type declarations still often have universe level metavariables.
They may appear anywhere:
- in types of inductive parameters/indices
- in the resulting universe level of the type former
- and in constructor fields (i.e. those parameters after inductive parameters).

The resulting universe has a strong bearing on what sort of inference we can do:
- If it is `Prop`, the type is an *inductive predicate*,
  and it is *impredicative*, meaning fields can come from any universe.
- Otherwise, fields are subject to the universe level inequality (described further below).

There are certain cases where we choose to infer `Prop` for the resulting universe.
Recall that an inductive type is a *syntactic subsingleton* if any two terms of that type
are definitionally equal. Syntactic subsingletons can eliminate into `Type`, hence can be pattern matched.
This justifies setting the resulting universe `Prop` if a type is "obviously" meant to be an inductive predicate.
Roughly, we say an inductive type is "obviously" meant to be an inductive predicate if the type
is not recursive, has exactly one constructor, the constructor has at least one field, and every field is `Prop`.
See `isPropCandidate` for further explanation.

From now on, we will talk only about inductive types in `Type` or above.

There are a number of considerations for inference:
- **The universe level inequality.** If `u` is the resulting universe level,
  then for every field `f : fty` of every constructor, we must have `v ≤ u`, where `fty : Sort v`.
- **Avoiding `Sort` polymorphism.**
  We say a type is `Sort`-polymorphic if, depending on the values of level parameters,
  the resulting universe can be both `Prop` and `Type _`.
  These usually cannot eliminate into `Prop` unless they are syntactic subsingletons,
  so we wish to avoid `Sort` polymorphism to avoid users' unpleasant surprises.
  We do this by adding the constraint `1 ≤ u`.
- **Using the minimal resulting universe** if it exists.
  If `u` has metavariables, then we do not want `u` to be unnecessarily large.
  We want to find the minimal levels to assign to the metavariables subject to the above constraints.
  However: we only entertain **unique** solutions. We report ambiguous situations to the user.
  Furthermore, this is **best-effort**. Users can always provide an explicit resulting universe.
  (We can also detect certain situations where this procedure computes a universe that is likely
  larger than what could be if it had been explicitly provided *before* constructor elaboration.)
- **Avoiding inferring proof fields**. If `v` is the universe level for a constructor field,
  then we avoid assigning metavariable in `v` to anything that could potentially give `Prop` fields
  or `Sort` polymorphism. To do this, we use the *weak* constraint `1 ≤w v`. Definition:
  - `1 ≤w p` and `1 ≤w k` for all parameters `p` and constants `k`.
  - `1 ≤w succ v` for all levels `v`
  - `1 ≤w max a b` and `1 ≤w imax a b` iff `1 ≤w a` and `1 ≤w b`
  - `1 ≤w ?v` iff `1 ≤ ?v`.
  The effect is that `1 ≤w v` resolves to a set of `1 ≤ ?v` metavariable constraints.
  This is more conservative than it needs to be, but it is uniform and avoids SAT-like reasoning;
  *effectively, inference analyzes each metavariable, independently from one another.*
- **Using the unique universe for fields** if it exists, preferring non-constant solutions.
  Uniqueness is with respect to the set of universe level expressions, not universe levels.
  Examples:
  - `?a ≤ 0` ~~~> `?a = 0` is the **unique solution**.
    (Note: this can lead to unpleasant surprises, where a field unexpectedly becomes a proof.
    We currently do nothing about this. It would require more careful global analysis.)
  - `?a ≤ 1` ~~~> either `?a = 0` or `?a = 1`, so **underconstrained** unless we have `1 ≤ ?a`,
    in which case `?a = 1` is the **unique solution**.
  - `?a ≤ v` with `v` a level parameter ~~~> syntactically have `?a = 0` and `?a = v` as solutions,
    but prefer `?a = v` since it is non-constant, and is the **unique solution**.
  - `?a ≤ v + 1` with `v` a level parameter ~~~> syntactically have `?a = 0`, `?a = 1`, `?a = v`, and `?a = v + 1`
    as solutions, with `?a = v` and `?a = v + 1` preferred. This is **underconstrained**,
    unless we have `1 ≤ ?a`, in which case `?a = v + 1` is the **unique solution**.
  - `?a ≤ max v₁ v₂` with `v₁` and `v₂` level parameters ~~~> syntactically have `?a = 0`, `?a = v₁`,
    `?a = v₂`, and `?a = max v₁ v₂` as solutions, with the latter three preferred. This is **underconstrained**.

  The heuristic for preferring non-constant solutions comes from user examples.

Collecting the constraints, these rules imply the only assignments considered are:

- if `0 ≤ ?a ≤ k`      and `k = 0` then assign `?a := 0`
- if `0 ≤ ?a ≤ p + k`  and `k = 0` then assign `?a := p`
- if `1 ≤ ?a ≤ k`      and `k = 1` then assign `?a := 1`
- if `1 ≤ ?a ≤ p + k`  and `k = 1` then assign `?a := p + 1`

Otherwise we do not assign `?a`, and we leave it to the "declaration has metavariables" error to report it.

There are also other considerations to make the inference more effective.
If the resulting universe is of the form `max ?m 1`, we want to isolate `?m` as
the metavariable to solve for.
The `simplifyResultingUniverse u` procedure is a heavy hammer to reliably extract
the "generic part" of the resulting universe level that is suitable for the inference procedures,
without the fragility of matching on specific patterns.
It gives a universe level `u' ≤ u` such that `u'` and `u` are equivalent "at infinity",
which means `u' = u` for all sufficiently high assignments of the parameters or metavariables.
In general, we only attempt solving for any universe levels at each stage
if `u'` is of the form `r + k` where `r` is a parameter, metavariable, or zero,
since in other cases solutions are not unique.

**High-level inference algorithm:**
- Solve for the metavariable in the resulting universe level.
- Solve for metavariables in constructor fields, if possible.
- Turn level metavariables in the type former (and from `collectExtraHeaderLMVars`) into level parameters.
- Report unsolved level metavariables.

Examples are in `tests/lean/run/inductive_univ.lean`.

-/

private def throwCannotInferResultingUniverse {α} (u : Level) (reason : MessageData) : TermElabM α :=
  throwError m!"\
    Cannot infer resulting universe level of inductive datatype: \
    {reason}{indentExpr <| mkSort u}"
    ++ .hint' "Provide the uninferred universe explicitly"

/--
Given a universe level `u`, computes a simplified representative `u' ≤ u` such that
`u` and `u'` are equivalent *at infinity*. This means that `u = u'` for all
sufficiently large assignments of parameters or metavariables in `u` and `u'`.
If `u` is non-constant, this procedure effectively removes the constant part.

The primary example is `max a b ≈ a` if `a` has variables and `b` is constant.
For example, `max ?u 1` and `?u` are equivalent at infinity, since they are equal for all `?u ≥ 1`.

Options:
- If `paramConst = true`, then parameters are treated like constants (only metavariables
  are considered to be varying).
-/
private partial def simplifyResultingUniverse (u : Level) (paramConst := false) : Level :=
  let varies (l : Level) := l.hasMVar || (!paramConst && l.hasParam)
  let simpAcc (acc : LevelMap Nat) : LevelMap Nat :=
    -- If there's a variable, then these dominate at infinity; constants can be eliminated
    if (acc.any fun l _ => varies l) then acc.filter (fun l _ => varies l) else acc
  let germMax (acc : LevelMap Nat) : Level :=
    (simpAcc acc).fold (init := levelZero) fun u l offset => mkLevelMax' u (l.addOffset offset)
  let accInsert (acc : LevelMap Nat) (u : Level) (offset : Nat) : LevelMap Nat :=
    acc.alter u (fun offset? => some (max (offset?.getD 0) offset))
  -- Simplifies `u+offset`, accumulating `max` arguments in `acc`.
  let rec simp (u : Level) (offset : Nat) (acc : LevelMap Nat) : LevelMap Nat :=
    match u with
    | .zero | .mvar _ | .param _ => accInsert acc u offset
    | .succ _ => simp u.getLevelOffset (offset + u.getOffset) acc
    | .max a b => simp b offset (simp a offset acc)
    | .imax a b =>
      if b.isAlwaysZero then
        accInsert acc levelZero offset
      else if a.isAlwaysZero || b.isNeverZero then
        simp b offset (simp a offset acc)
      else
        /- The remaining simplification we consider is when `a ≤ b` then `imax a b = b`.
        We can compute `a ≤ b` by checking `max a b = b`.
        We only need `max a b ≈ b` for this,
        since `b ≤ imax a b ≤ max a b ≈ b` implies `imax a b ≈ b`. -/
        let acca := simp a 0 {}
        let accb := simp b 0 {}
        let accab := simpAcc (acca.fold (init := accb) accInsert)
        if accab.all (fun l n => if let some m := accb[l]? then n ≤ m else false) then
          accb.fold (init := acc) fun acc l n => accInsert acc l (n + offset)
        else
          accInsert acc (Level.imax (germMax acca) (germMax accb)) offset
  germMax (simp u 0 {})

/--
Checks that `u` has at most one universe level metavariable.
If it has a level metavariable, then applies the `simplifyResultingUniverse`
procedure to it and checks that the result is of the form `?m + k`.
Returns the simplified universe — this is used as an upper bound when collecting constraints
to solve for a least `?m`.

Throws an exception if `u` has metavariables and isn't of the right form for inference.
-/
private def processResultingUniverseForInference (u : Level) : TermElabM Level := do
  if u.hasMVar then
    unless u.collectMVars.size == 1 do
      throwCannotInferResultingUniverse u m!"The resulting universe contains more than one metavariable"
    -- Simplify the universe level and see if we get `?m + k`.
    -- We treat parameters is constants since, for example, simplifying `(max u ?m) + k` to `?m + k`
    -- does not change the solvability of the constraints.
    let u' := simplifyResultingUniverse u.normalize (paramConst := true)
    if u'.getLevelOffset.isMVar then
      trace[Elab.inductive] "resulting universe: {u}, simplified universe: {u'}"
      return u'
    else
      throwCannotInferResultingUniverse u m!"\
        The resulting universe contains a level metavariable but is not in a form suitable for inference"
  else
    return u


private structure AccLevelState where
  /--
  The constraint `u ≤ ?r + k` is represented by `levels[u] := k`.
  When `k` is negative, this represents `u + (-k) ≤ ?r`.
  The level `u` is either a parameter, metavariable, or `levelZero`.

  When `k ≥ 0`, this is potentially a "bad" level constraint.
  -/
  levels : LevelMap Int := {}

private def AccLevelState.push (acc : AccLevelState) (u : Level) (offset : Int) : AccLevelState :=
  let offset := min (acc.levels.getD u offset) offset
  { acc with levels := acc.levels.insert u offset }

/--
Auxiliary function for `inferResultingUniverse`.
Consider the constraint `u ≤ ?r + rOffset`.
This function simplifies the constraints in an attempt to find a minimal solution
of the form `?r := max l₁ ... lₙ` where each `lᵢ` is normalized and not a `max`/`imax`.

In the calculation, we allow negative values of `rOffset`. For example, `u ≤ ?r - 4` means `u + 4 ≤ ?r`.

The `typeLMVarIds` array is all the level mvars that appear in all the type formers in an inductive family.
All other level mvars are ignored — the idea is that type former level mvars can become level parameters,
but constructor level mvars need to be inferred separately.

Positive values of `rOffset` tend to correspond to "too big" of an inferred universe.
Consider `u ≤ ?r + 1`, which is a constraint that comes from the example
```lean
inductive I (α : Sort u) : Type _ where
  | mk (x : α)
```
This is likely a mistake. The best solution would be `Sort (max u 1)` rather than `Type (u + 1)`,
but by this point in elaboration it is impossible to rectify.
So, for `u ≤ ?r + 1` we record both `u` and `1`
to be able to inform the user what they should have probably used instead.
-/
private def accLevel (u : Level) (r : Level) (rOffset : Nat) (typeLMVarIds : Array LMVarId) :
    ExceptT MessageData (StateT AccLevelState Id) Unit := do
  go u.normalize rOffset
where
  /-- `u ≤ ?r + rOffset` -/
  go (u : Level) (rOffset : Int) : ExceptT MessageData (StateT AccLevelState Id) Unit := do
    match u with
    | .max u v          => go u rOffset; go v rOffset
    | .imax u v         => go u rOffset; go v rOffset
    | .param ..         => modify fun acc => acc.push u rOffset
    | .succ u           => go u (rOffset - 1)
    | .zero =>
      /- `0 ≤ ?r + rOffset` always holds for non-negative `rOffset` values. -/
      if rOffset < 0 then
        modify fun acc => acc.push .zero rOffset
    | .mvar lmvarId =>
      if u == r then
        /- `?r ≤ ?r + rOffset` always holds for non-negative `rOffset` values,
        but `?r + (-rOffset) ≤ ?r` is impossible. -/
        if rOffset < 0 then
          throw m!"Level inequality `{Level.addOffset r rOffset.natAbs} ≤ {r}` is inconsistent."
      else if typeLMVarIds.contains lmvarId then
        modify fun acc => acc.push u rOffset
      else if rOffset < 0 then
        modify fun acc => acc.push .zero rOffset

/--
Auxiliary function for `inferResultingUniverse`. Applies `accLevel` to the given constructor parameter.
-/
private def accLevelAtCtor (ctorParam : Expr) (r : Level) (rOffset : Nat) (typeLMVarIds : Array LMVarId) :
    StateT AccLevelState TermElabM Unit := do
  let type ← inferType ctorParam
  let u ← instantiateLevelMVars (← getLevel type)
  match (← modifyGet fun s => accLevel u r rOffset typeLMVarIds |>.run |>.run s) with
  | .ok _ => pure ()
  | .error msg =>
    throwError "Failed to infer universe level for resulting type due to the constructor argument `{ctorParam}`: {msg}"

/--
Auxiliary function for `inferResultingUniverse`. Applies `accLevelAtCtor` to each constructor.
-/
private def collectUniverseConstraints (views : Array InductiveView) (r : Level) (rOffset : Nat)
      (numParams : Nat) (indTypes : List InductiveType) (typeLMVarIds : Array LMVarId) :
    TermElabM AccLevelState := do
  let (_, acc) ← go |>.run {}
  return acc
where
  go : StateT AccLevelState TermElabM Unit :=
    indTypes.forM fun indType => indType.ctors.forM fun ctor =>
      withCtorRef views ctor.name do
        forallTelescopeReducing ctor.type fun ctorParams _ =>
          for ctorParam in ctorParams[numParams...*] do
            accLevelAtCtor ctorParam r rOffset typeLMVarIds

/--
Decides whether the inductive type should be `Prop`-valued when the universe is not given.

Heuristic:
- We want `Prop` when each inductive type is obviously a syntactic subsingleton.
  That's to say, when each inductive type has at most one constructor, and each field is a `Prop`.
  Such types carry no data anyway.
- Exception: if no inductive type has any constructors, these are likely stubbed-out declarations,
  so we prefer `Type` instead.
- Exception: if each constructor has no parameters, then these are likely partially-written enumerations,
  so we prefer `Type` instead.

When ppecialized to structures, the heuristic is that we prefer a `Prop` instead of a `Type` structure
when it could be a syntactic subsingleton.
Exception: no-field structures are `Type` since they are likely stubbed-out declarations.
-/
private def isPropCandidate (numParams : Nat) (indTypes : List InductiveType) (indFVars : Array Expr) : MetaM Bool := do
  -- Every inductive type has at most one constructor, and there's at least one constructor among them:
  unless (indTypes |>.map (·.ctors.length) |>.foldl max 0) == 1 do
    return false
  let mut hasCtorField := false
  for indType in indTypes do
    for ctor in indType.ctors do
      -- `fields` is an array capturing the suitability of each field
      -- 1. they must be proofs
      -- 2. they must not refer to any of the inductive types being defined
      let fields ← forallTelescopeReducing ctor.type fun ctorParams _ => do
        ctorParams[numParams...*].toArray.mapM fun field => do
          let fieldTy ← inferType field >>= instantiateMVars
          Meta.isProof field <&&> pure (not <| fieldTy.hasAnyFVar (indFVars.contains <| .fvar ·))
      unless fields.all id do
        return false
      hasCtorField := hasCtorField || fields.size > 0
  return hasCtorField

/--
We don't assign the metavariable in the resulting universe right away in `inferResultingUniverse`.
The issue is that there may be level metavariables in the assignment that will eventually become
parameters, and we want to be sure we assign once we can normalize the level being assigned.
-/
private structure ResultingUniverseResult where
  /-- Inferred resulting universe -/
  u : Level
  /-- Assignment to do once all level metavariables in `Level` are converted to parameters. -/
  assign? : Option (LMVarId × Level)

/-- Performs the assignment that may be recorded in the result, while normalizing the level. -/
private def ResultingUniverseResult.assign (res : ResultingUniverseResult) : MetaM Unit := do
  match res.assign? with
  | some (mvarId, level) =>
    assignLevelMVar mvarId (← instantiateLevelMVars level).normalize
  | none =>
    pure ()

/--
Given that the resulting type is of the form `Sort u` where `u` contains a single metavariable `?r`,
and if `univForInfer` is the result of `processResultingUniverseForInference` and is of the form `?r + k`,
then try to infer the minimal `?r` such that `?r + k` is the supremum of the constructor arguments' universe levels, if one exists.

Usually, we also throw in the constraint that `1 ≤ ?r + k`, but if `isPropCandidate` is true we allow the solution `u = 0`.
-/
private def inferResultingUniverse (views : Array InductiveView)
    (numParams : Nat) (indTypes : List InductiveType) (indFVars : Array Expr) (typeLMVarIds : Array LMVarId) :
    TermElabM ResultingUniverseResult := do
  let u ← getResultingUniverse indTypes >>= instantiateLevelMVars
  -- For `Prop` candidates, need to examine `u` itself, rather than `univForInfer` (which has been simplified).
  if let Level.mvar mvarId := u.normalize then
    if ← isPropCandidate numParams indTypes indFVars then
      -- May as well assign now, since `levelZero` is already normalized.
      assignLevelMVar mvarId levelZero
      return { u := u, assign? := none }
  -- Proceed with non-`Prop`-candidate case.
  let univForInfer ← withViewTypeRef views <| processResultingUniverseForInference u
  let r@(Level.mvar mvarId) := univForInfer.getLevelOffset | return { u := u, assign? := none }
  let rOffset := univForInfer.getOffset
  /- Collect universe level constraints -/
  let acc ← collectUniverseConstraints views r rOffset numParams indTypes typeLMVarIds
  -- Add `1 ≤ ?r + rOffset` if `rOffset = 0`.
  let acc := if rOffset == 0 then acc.push .zero (-1) else acc
  -- Filter the accumulated constraints for the ones that are not already satisfied.
  let rConstraints := acc.levels.fold (init := []) fun parts l k =>
    /-
    The constraint is `l ≤ ?r + k`, where `k` might be negative.
    Adding `rOffset - k` to both sides gets the "ideal" constraint `l + (rOffset - k) ≤ ?r + rOffset`.
    If `l + (rOffset - k) ≤ u` already, we do not need to incorporate it.
    -/
    if u.geq (l.addOffset (rOffset - k).toNat) then
      parts
    else
      (l, k) :: parts
  trace[Elab.inductive] "inferResultingUniverse r: {r}, rOffset: {rOffset}, rConstraints: {rConstraints}"
  /- Compute the inferred `r` -/
  let rInferred := Level.normalize <| rConstraints.foldl (init := levelZero) fun u' (level, k) =>
    -- If `k ≤ 0`, then add `level + (-k) ≤ ?r` constraint, otherwise add `level ≤ ?r`.
    mkLevelMax' u' <| level.addOffset (-k).toNat
  let uInferred := (u.replace fun v => if v == r then some rInferred else none).normalize
  /- Analyze "bad" constraints if there are any, and report an error if needed. -/
  if rConstraints.any (fun (_, k) => k > 0) then
    let uAtZero := u.replace fun v => if v == r then some levelZero else none
    /- For "bad" level constraints (those of the form `l ≤ ?r + k` where `k > 0`),
    we add `rOffset - k` to both sides to get the ideal constraint. -/
    let uIdeal := Level.normalize <| rConstraints.foldl (init := uAtZero) fun u' (level, k) =>
      mkLevelMax' u' <| level.addOffset (rOffset - k).toNat
    unless uIdeal.geq uInferred do
      withViewTypeRef views do
        let badConstraints := rConstraints.foldl (init := []) fun msgs (level, k) =>
          if k <= 0 then
            msgs
          else
            indentD m!"{level} ≤ {Level.addOffset r k.toNat}" :: msgs
        logWarning <| m!"Inferred universe level for type may be unnecessarily high. \
          The inferred resulting universe is{indentD <| mkSort uInferred}\n\
          but it possibly could be{indentD <| mkSort uIdeal}\n\
          Explicitly providing a resulting universe with no metavariables will silence this warning."
          ++ .note m!"The elaborated resulting universe after constructor elaboration is{indentD <| mkSort u}\n\
            The inference algorithm attempts to compute the smallest level for `{r}` such that all universe constraints for all \
            constructor fields are satisfied, with some approximations. \
            The following derived constraint(s) are the cause of this possible unnecessarily high universe:\
            {MessageData.joinSep badConstraints ""}\n\
            For example, if the resulting universe is of the form `Sort (?r + 1)` and a constructor field is in universe `Sort u`, \
            the constraint `u ≤ ?r + 1` leads to the unnecessarily high resulting universe `Sort (u + 1)`. \
            Using `Sort (max 1 u)` avoids this universe bump, if using it is possible."
  trace[Elab.inductive] "inferred r: {rInferred}"
  return { u := uInferred, assign? := some (mvarId, rInferred) }

/--
Solves for level metavariables in constructor argument types that are completely determined by the resulting type.
The `simplifyResultingUniverse` of the resulting universe level `u` must be of the form `r+k`, where `r` is a parameter or zero,
otherwise inference is ambiguous.
Ambiguity example: `?v ≤ max a b` could be satisfied by either constraint `?v ≤ a` or `?v ≤ b`.
Possibly `r` is a metavariable -- in that case, since it will eventually be turned into a parameter
in `levelMVarToParamAtInductives`, we work with it as if it is a parameter here.

This only assigns if there is a *unique* solution, though we will take a non-constant solution over
a constant one. This function does not throw errors. For underconstrained metavariables it simply
doesn't assign to them. Even constraint issues are ignored, since these will be reported later.
We also assume that `imax` is effectively `max`.

The rules imply that the only assignments we will ever consider are `?v = 0` or `?v = r`.
From each universe constraint, we get simple constraints of the form `?v ≤ r + k'`,
with `k' : Int` like in `inferResultingUniverse`.
Consider the cases:
- if `r=0`, then we must have `k'≥0` to have a solution, and `k'≤0` to have a unique solution.
- if `r` is a parameter, then if `k'>0` there are multiple non-constant solutions, and if
  `k'<0` then there are no solutions that work for all values of `r`. We must have `k'=0`.
Thus, the solution to such simple constraints is always `?v = r` if `k' = 0`.

One wrinkle to this is that we wish to avoid assigning `?u = 0` in some cases due examples like the following
that lead to counterintuitive behavior:
```
inductive Bar : Type
| foobar {Foo} : Foo → Bar
```
Since `Foo : Sort ?u : Type ?u`, propagation causes `?u = 0`, and so `Foo : Prop`.
We avoid assigning level metavariables to `0` if it could cause a field to become a `Prop`.
-/
private partial def propagateUniversesToConstructors
    (numParams : Nat) (indTypes : List InductiveType) (inferResult : ResultingUniverseResult):
    TermElabM Unit := do
  let u := (← instantiateLevelMVars inferResult.u).normalize
  if u.isZero then
    return
  let u' := simplifyResultingUniverse u
  let r := u'.getLevelOffset
  let k := u'.getOffset
  unless r matches .param .. | .mvar .. | .zero do
    trace[Elab.inductive] "skipping propagating universe levels to constructors, simplified resulting type {u'} is not of form u+k or k"
    return
  trace[Elab.inductive] "propagating universe levels to constructors using simplified resulting type {u'}"
  let (_, constraints, loConstraint) ← collectConstraints r k |>.run ({}, {})
  trace[Elab.inductive] "collected constraints: {constraints.levels.toList}; positive: {loConstraint.toList.map Level.mvar}"
  for (v, k') in constraints.levels do
    -- `v ≤ r + k'` has solutions `v ∈ {r, r + 1, ..., r + k'}`,
    -- excluding the constant solutions when `r` is a parameter.
    -- If `hasLo` is true, then we want `1 ≤ v` as well.
    -- There's a unique solution if `k'=0` or `k'=1`, depending on the value of `hasLo`.
    let hasLo := loConstraint.contains v.mvarId!
    if k' == (if hasLo then 1 else 0) then
      assignLevelMVar v.mvarId! (r.addOffset k'.toNat)
where
  collectConstraints (r : Level) (k : Int) :
      StateT (AccLevelState × LMVarIdSet) MetaM Unit := do
    indTypes.forM fun indType => indType.ctors.forM fun ctor =>
      forallTelescopeReducing ctor.type fun ctorArgs _ => do
        for ctorArg in ctorArgs[numParams...*] do
          let v := (← instantiateLevelMVars (← getLevel (← inferType ctorArg))).normalize
          extractConstraints v r k 1
  /--
  Extract level constraints from `v ≤ r + k` for metavariables in `v`.
  `Level.imax` can repush itself onto the `LevelConstraintForPropagate` work list.
  -/
  extractConstraints (v : Level) (r : Level) (k : Int) (lo : Nat) :
      StateT (AccLevelState × LMVarIdSet) MetaM Unit := do
    if v.hasMVar then
      match v with
      | .zero | .param .. => pure ()
      | .succ _ => extractConstraints v.getLevelOffset r (k - v.getOffset) 0
      | .max a b => extractConstraints a r k lo; extractConstraints b r k lo
      /-
      Given `imax a b ≤ r + k`, then certainly `b ≤ r + k`.
      We only get the additional constraint `a ≤ r + k` when `b > 0`.
      However, for our simple constraint propagation system, we do not want to be
      responsible for deciding whether or not we need `b = 0` for the purpose of satisfying constraints.
      Heuristic: Since we're aiming for `b ≥ lo`, if `lo > 0` then we assume the `imax` will simplify to `max`.
      -/
      | .imax a b =>
        if lo > 0 then
          extractConstraints a r k lo
        extractConstraints b r k lo
      | .mvar mvarId =>
        if v != r then
          modify fun (acc, los) => (acc.push v k, if lo > 0 then los.insert mvarId else los)

/--
Converts universe metavariables in the type (not the constructors) into new parameters.
The additional level parameters in `typeLMVarIds` can be promoted to level metavariables
if they appear among the constructors.
-/
private def levelMVarToParamAtInductives
    (indTypes : List InductiveType) (typeLMVarIds : Array LMVarId) (resultUniv : ResultingUniverseResult) :
    TermElabM Unit := do
  let rmvarId? := resultUniv.assign?.map (fun (mvarId, _) => mvarId)
  indTypes.forM fun indType => do
    discard <| Term.levelMVarToParam indType.type (except := fun mvar => rmvarId? == some mvar)
    if rmvarId?.isSome then
      -- Hasn't been assigned, so be sure to visit full resulting universe level
      discard <| Term.levelMVarToParam (mkSort resultUniv.u)
    indType.ctors.forM fun ctor => do
      discard <| Term.levelMVarToParam ctor.type (except := fun mvar => rmvarId? == some mvar || !typeLMVarIds.contains mvar)

end LevelInference

/--
Heuristic: users don't tend to want types that are universe polymorphic across both `Prop` and `Type _`.
This can be disabled by setting the option `bootstrap.inductiveCheckResultingUniverse` to false,
unless one of the inductive commands requires it (for instance `structure` due to projections).
-/
private def checkResultingUniversePolymorphism (views : Array InductiveView) (u : Level) (_numParams : Nat) (_indTypes : List InductiveType) : TermElabM Unit := do
  let doErrFor := fun view =>
    view.withTypeRef do
      throwError m!"\
        Invalid universe polymorphic resulting type: The resulting universe is not `Prop`, but it may be `Prop` for some parameter values:{indentD (mkSort u)}"
        ++ .hint' m!"A possible solution is to use levels of the form `max 1 _` or `_ + 1` to ensure the universe is of the form `Type _`"
  unless u.isZero || u.isNeverZero do
    for view in views do
      if !view.allowSortPolymorphism then
        doErrFor view
    if bootstrap.inductiveCheckResultingUniverse.get (← getOptions) then
      -- TODO: heuristic for allowing `Sort` polymorphism?
      doErrFor views[0]!

/-- Checks the universe constraints for each constructor. -/
private def checkResultingUniverses (views : Array InductiveView) (elabs' : Array InductiveElabStep2)
    (numParams : Nat) (indTypes : List InductiveType) : TermElabM Unit := do
  let u := (← instantiateLevelMVars (← getResultingUniverse indTypes)).normalize
  checkResultingUniversePolymorphism views u numParams indTypes
  unless u.isZero do
    for h : i in *...indTypes.length do
      let indType := indTypes[i]
      -- See if there is a custom error. If so, this should throw an error first:
      elabs'[i]!.checkUniverses numParams u
      indType.ctors.forM fun ctor =>
      forallTelescopeReducing ctor.type fun ctorArgs _ => do
        for ctorArg in ctorArgs[numParams...*] do
          let type ← inferType ctorArg
          let v := (← instantiateLevelMVars (← getLevel type)).normalize
          unless u.geq v do
            let mut msg := m!"Invalid universe level in constructor `{ctor.name}`: Parameter"
            unless (← ctorArg.fvarId!.getUserName).hasMacroScopes do
              msg := msg ++ m!" `{ctorArg}`"
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
  for h : i in *...views.size do
    let view    := views[i]
    let indFVar := indFVars[i]!
    m := m.insert indFVar (mkConst view.declName levelParams)
  return m

/-- Remark: `numVars <= numParams`. `numVars` is the number of context `variables` used in the inductive declaration,
   and `numParams` is `numVars` + number of explicit parameters provided in the declaration. -/
private def replaceIndFVarsWithConsts (views : Array InductiveView) (indFVars : Array Expr) (levelNames : List Name)
    (numVars : Nat) (numParams : Nat) (indTypes : List InductiveType) (applyVariables : Bool := true) : TermElabM (List InductiveType) :=
  let indFVar2Const := mkIndFVar2Const views indFVars levelNames
  indTypes.mapM fun indType => do
    let ctors ← indType.ctors.mapM fun ctor => do
      let type ← forallBoundedTelescope ctor.type numParams fun params type => do
        let type := type.replace fun e =>
          if !e.isFVar then
            none
          else match indFVar2Const[e]? with
            | none   => none
            | some c => if applyVariables then mkAppN c (params.extract 0 numVars) else c
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

private structure FinalizeInductiveDecl where
  decl : Declaration
  indFvars : Array Expr
  numParams : Int
  rs : Array PreElabHeaderResult

/--
  For nested inductive types, the kernel adds a variable number of auxiliary recursors.
  Let the elaborator know about them as well. (Other auxiliaries have already been
  registered by `addDecl` via `Declaration.getNames`.)
  NOTE: If we want to make inductive elaboration parallel, this should switch to using
  reserved names.
-/
private def addAuxRecs (indTypes : List InductiveType) : TermElabM Unit := do
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

private def mkReplaceIndFVars (views : Array InductiveView) (indFVars : Array Expr)
   (levelParams : List Name) (vars : Array Expr) : Expr → MetaM Expr := fun e => do
    let indFVar2Const := mkIndFVar2Const views indFVars levelParams
    return (← instantiateMVars e).replace fun e' =>
      if !e'.isFVar then
        none
      else
        match indFVar2Const[e']? with
        | none   => none
        | some c => mkAppN c vars

private def buildFinalizeContext (elabs' : Array InductiveElabStep2) (levelParams : List Name)
    (vars params : Array Expr) (views : Array InductiveView) (newIndFVars : Array Expr)
    (rs : Array ElabHeaderResult) : TermElabM FinalizeContext := do
  let lctx := rs.foldl (init := ← getLCtx) fun lctx r =>
    lctx.modifyLocalDecl r.indFVar.fvarId! fun decl =>
      decl.setUserName (`_indFVar ++ decl.userName)

  pure {
    elabs := elabs',
    levelParams,
    params := vars ++ params,
    replaceIndFVars := mkReplaceIndFVars views newIndFVars levelParams vars,
    mctx := ← getMCtx,
    lctx,
    localInsts := ← getLocalInstances
  }

def replaceIndFVars (numParams : Nat) (oldFVars : Array Expr) (calls : Array Expr) : Expr → Expr := fun e =>
  let replacementMap : ExprMap Expr := {}
  let replacementMap := replacementMap.insertMany <| oldFVars.zip calls
  e.replace (fun e =>
    if e.isApp || numParams == 0 then
      if let some replacement := replacementMap.get? e.getAppFn then
        mkAppN replacement <| e.getAppArgs.extract numParams
      else
        .none
    else
      .none
    )

private def ensureNoUnassignedMVarsAtInductives (indTypes : List InductiveType) :
    TermElabM Unit := do
  let mut mvars := {}
  for indType in indTypes do
    mvars := indType.type.collectMVars mvars
    for ctor in indType.ctors do
      mvars := ctor.type.collectMVars mvars
  let pendingMVarIds := mvars.result
  if (← Term.logUnassignedUsingErrorInfos pendingMVarIds) then
    throwAbortCommand

private def ensureNoUnassignedLevelMVarsAtInductives
    (views : Array InductiveView) (indTypes : List InductiveType) :
    TermElabM Unit := do
  let mut lmvars := {}
  for indType in indTypes do
    lmvars := collectLevelMVars lmvars indType.type
    for ctor in indType.ctors do
      lmvars := collectLevelMVars lmvars ctor.type
  let pendingLevelMVars := lmvars.result
  unless pendingLevelMVars.isEmpty do
    if (← Term.logUnassignedLevelMVarsUsingErrorInfos pendingLevelMVars) then
      throwAbortCommand
    else if (← MonadLog.hasErrors) then
      throwAbortCommand
    else
      -- This is a fallback in case we don't have an error info available for the universe level metavariables.
      -- We try to produce an error message containing an expression with one of the universe level metavariables.
      for view in views, indType in indTypes do
        withRef view.ref do
          Term.forEachExprWithExposedLevelMVars indType.type fun e => do
            throwError "\
              Inductive type declaration `{view.declName}` contains universe level metavariables at the expression\
              {indentExpr e}\n\
              in the type{indentExpr <| ← Term.exposeLevelMVars indType.type}"
          for ctorView in view.ctors, ctor in indType.ctors do
            withRef ctorView.ref <| forallTelescope ctor.type fun args ctype => do
              for arg in args do
                let argTy ← inferType arg
                Term.forEachExprWithExposedLevelMVars argTy fun e => do
                  throwError "\
                    Constructor field `{arg}` of `{ctorView.declName}` contains universe level metavariables at the expression\
                    {indentExpr e}\n\
                    in its type{indentExpr <| ← Term.exposeLevelMVars argTy}"
              Term.forEachExprWithExposedLevelMVars ctype fun e => do
                throwError "\
                  Constructor `{ctorView.declName}` contains universe level metavariables at the expression\
                  {indentExpr e}\n\
                  in the type{indentExpr <| ← Term.exposeLevelMVars ctype}"

/--
  Given a list of `InductiveType` structures and some local variables of `mkInductiveDecl`,
  rewrites the inductive types and their constructors in a way that signature contains parameters
  representing the types being defined, and all the recursive occurrences of the inductive types
  in constructor are replaced by applications of these parameters.

  This function is used to implement coinductive predicates. For more details, see the comment in
  `Elab.Coinductive`

  Upon rewriting the inductive types, it adds the new inductive declaration to the environment,
  following the same pattern as `mkInductiveDecl`.

  We assume that numVars <= numParams, where numVars is the number of local variables.
-/
private def mkFlatInductive (views : Array InductiveView)
  (indFVars : Array Expr) (levelParams : List Name) (numVars : Nat)
  (numParams : Nat) (indTypes : List InductiveType) : TermElabM Unit := do

  let namesAndTypes := indTypes.map fun indType => (indType.name.append `call, indType.type)
  let namesAndTypes := namesAndTypes.toArray

  -- We update the type of all inductive types, so they have recursive calls added as parameters
  let newTypes ← namesAndTypes.mapM fun (_, indType) =>
    forallBoundedTelescope indType numParams fun indTypeParams indTypeBody => do

      -- We first go through all types in the mutual block and get rid of their parameters
      -- by substituting free variables
      let typesWithAppliedParams ← namesAndTypes.mapM fun (newName, curIndType) => do
        forallBoundedTelescope curIndType numParams fun curIntTypeParams curIndTypeBody => do
          return (newName, curIndTypeBody.replaceFVars curIntTypeParams indTypeParams)
      withLocalDeclsDND typesWithAppliedParams fun newParams => do
       mkForallFVars (indTypeParams ++ newParams) indTypeBody
  let rs ← newTypes.mapIdxM fun idx newType => do
    return PreElabHeaderResult.mk views[idx]! levelParams (numParams + views.size) newType #[]

  -- We now reuse the machinery for bringing in indFVars to the context
  withInductiveLocalDecls rs fun newParams newIndFVars => do
    let indTypes ← indTypes.mapIdxM fun indTypeIdx indType => do
      let updatedCtors ← indType.ctors.mapM fun ctor => do
        -- We first use new set of parameters
        let updatedCtor ← instantiateForall ctor.type (newParams.take numParams)
        let updatedCtor ← forallTelescope updatedCtor fun ctorArgs ctorBody => do
            -- We assume that the conclusion is an application of the fvar
          guard <| ctorBody.isApp || numParams == 0

          -- We first get non-parameter arguments of the body
          let bodyArgs := ctorBody.getAppArgs.extract (numParams - numVars)

          -- And make a new conclusion with new indFVar. We pass new parameters and old non-parameter arguments
          let ctorBody := mkAppN (newIndFVars[indTypeIdx]!) (newParams ++ bodyArgs)
          mkForallFVars ctorArgs ctorBody

        -- Then we replace indFVars in the premises of the rule
        let calls := newParams.extract numParams
        let updatedCtor := replaceIndFVars (numParams - numVars) indFVars calls updatedCtor

        -- Finally, we need to abstract away the parameters
        let updatedCtor ← mkForallFVars newParams updatedCtor
        return { ctor with type := updatedCtor}
      return { indType with type := newTypes[indTypeIdx]!, ctors := updatedCtors}

    let indTypes ← replaceIndFVarsWithConsts views newIndFVars levelParams numVars (numParams + views.size) indTypes (applyVariables := false)
    let decl := Declaration.inductDecl levelParams (numParams + views.size) indTypes false
    Term.ensureNoUnassignedMVars decl
    addDecl decl

private structure AddAndFinalizeContext where
  views : Array InductiveView
  elabs' : Array InductiveElabStep2
  indFVars : Array Expr
  vars : Array Expr
  levelParams : List Name
  numVars : Nat
  numParams : Nat
  indTypes : List InductiveType
  isUnsafe : Bool
  rs : Array ElabHeaderResult
  params : Array Expr
  isCoinductive : Bool

private def addAndFinalizeInductiveDecl (context : AddAndFinalizeContext) : TermElabM FinalizeContext := do
    let indTypes ← replaceIndFVarsWithConsts context.views context.indFVars context.levelParams context.numVars context.numParams context.indTypes
    let decl := Declaration.inductDecl context.levelParams context.numParams indTypes context.isUnsafe
    Term.ensureNoUnassignedMVars decl
    addDecl decl
    addAuxRecs indTypes
    buildFinalizeContext context.elabs' context.levelParams context.vars context.params context.views context.indFVars context.rs

private def addTermInfoViews (views : Array InductiveView) : TermElabM Unit := -- save new env
  withSaveInfoContext do -- save new env
    for view in views do
      do Term.addTermInfo' view.declId (← mkConstWithLevelParams view.declName) (isBinder := true)
      for ctor in view.ctors do
        if (ctor.declId.getPos? (canonicalOnly := true)).isSome then do
          Term.addTermInfo' ctor.declId (← mkConstWithLevelParams ctor.declName) (isBinder := true)
          enableRealizationsForConst ctor.declName

private def mkInductiveDeclCore
  (callback : AddAndFinalizeContext → TermElabM α) (vars : Array Expr)
  (elabs : Array InductiveElabStep1) (rs : Array PreElabHeaderResult) (scopeLevelNames : List Name) : TermElabM α := do
  let views := elabs.map (·.view)
  let view0 := views[0]!
  let isCoinductive := views.any (·.isCoinductive)
  if isCoinductive then
    if let some i ← rs.findIdxM? (forallTelescopeReducing ·.type fun _ body => pure !body.isProp) then
      throwErrorAt views[i]!.declId "`coinductive` keyword can only be used to define predicates"
  let allUserLevelNames := rs[0]!.levelNames
  let isUnsafe          := view0.modifiers.isUnsafe
  withInductiveLocalDecls rs fun params indFVars => do
    trace[Elab.inductive] "indFVars: {indFVars}"
    /- Start elaborating constructors: -/
    let rs := Array.zipWith (fun r indFVar => { r with indFVar : ElabHeaderResult }) rs indFVars
    let mut indTypesArray : Array InductiveType := #[]
    let mut elabs' := #[]
    for h : i in *...views.size do
      Term.addLocalVarInfo views[i].declId indFVars[i]!
      let r     := rs[i]!
      let elab' ← elabs[i]!.elabCtors rs r params
      elabs'    := elabs'.push elab'
      indTypesArray := indTypesArray.push { name := r.view.declName, type := r.type, ctors := elab'.ctors }
    Term.synthesizeSyntheticMVarsNoPostponing
    let indTypes ← indTypesArray.toList.mapM instantiateMVarsAtInductive
    /- Constructor elaboration complete. -/
    /- Start parameter analysis:
       Every used section variable becomes a parameter,
       and the largest prefix of indices that are used like parameters are promoted to parameters. -/
    let numExplicitParams ← fixedIndicesToParams params.size indTypes indFVars
    trace[Elab.inductive] "numExplicitParams: {numExplicitParams}"
    withUsed elabs' vars indTypes fun vars => do
      let numVars   := vars.size
      let numParams := numVars + numExplicitParams
      let indTypes ← updateParams vars indTypes
      let indTypes ← indTypes.mapM instantiateMVarsAtInductive
      /- Parameter analysis complete. -/
      -- If there are expression metavariables, we should raise an error before attempting to infer universes.
      ensureNoUnassignedMVarsAtInductives indTypes
      /- Start universe inference. -/
      -- allow general access to private data with `withoutExporting` to compute universe levels;
      -- even though we are elaborating here, this can only leak universe level information
      let indTypes ← withoutExporting do
        let typeLMVarIds ← do
          let mut lmvars := {}
          for indType in indTypes do
            lmvars := collectLevelMVars lmvars indType.type
          lmvars ← Prod.snd <$> (elabs'.forM InductiveElabStep2.collectExtraHeaderLMVars).run lmvars
          pure lmvars.result
        let inferResult ← inferResultingUniverse views numParams indTypes indFVars typeLMVarIds
        propagateUniversesToConstructors numParams indTypes inferResult
        levelMVarToParamAtInductives indTypes typeLMVarIds inferResult
        inferResult.assign
        indTypes.mapM instantiateMVarsAtInductive
      /- Universe inference complete. -/
      -- allow general access to private data with `withoutExporting` while we do last universe checks
      withoutExporting do
        elabs'.forM fun elab' => elab'.finalizeTermElab
        ensureNoUnassignedLevelMVarsAtInductives views indTypes
        checkResultingUniverses views elabs' numParams indTypes
      let usedLevelNames := collectLevelParamsInInductive indTypes
      match sortDeclLevelParams scopeLevelNames allUserLevelNames usedLevelNames with
      | .error msg      => throwErrorAt view0.declId msg
      | .ok levelParams =>
        callback {
          views := views
          elabs' := elabs'
          indFVars := indFVars
          vars := vars
          levelParams := levelParams
          indTypes := indTypes
          isUnsafe := isUnsafe
          rs := rs
          params := params
          isCoinductive := isCoinductive
          numVars := numVars
          numParams := numParams
        }

private def withElaboratedHeaders (vars : Array Expr) (elabs : Array InductiveElabStep1)
  (k : Array Expr → Array InductiveElabStep1 → Array PreElabHeaderResult → List Name → TermElabM α ) : TermElabM α :=
Term.withoutSavingRecAppSyntax do
  let views := elabs.map (·.view)
  let view0 := views[0]!
  let scopeLevelNames ← Term.getLevelNames
  InductiveElabStep1.checkLevelNames views
  let allUserLevelNames := view0.levelNames
  withRef view0.ref <| Term.withLevelNames allUserLevelNames do
    let rs ← elabHeaders views
    Term.synthesizeSyntheticMVarsNoPostponing
    ElabHeaderResult.checkLevelNames rs
    trace[Elab.inductive] "level names: {allUserLevelNames}"
    k vars elabs rs scopeLevelNames

private def mkInductiveDecl (vars : Array Expr) (elabs : Array InductiveElabStep1) : TermElabM FinalizeContext :=
  withElaboratedHeaders vars elabs fun vars elabs rs scopeLevelNames => do
    let res ← mkInductiveDeclCore addAndFinalizeInductiveDecl vars elabs rs scopeLevelNames
    return res

private def mkAuxConstructions (declNames : Array Name) : TermElabM Unit := do
  let env ← getEnv
  let hasEq   := env.contains ``Eq
  let hasHEq  := env.contains ``HEq
  let hasUnit := env.contains ``PUnit
  let hasProd := env.contains ``Prod
  let hasNat  := env.contains ``Nat
  for n in declNames do
    mkRecOn n
    if hasUnit then mkCasesOn n
    if hasNat then mkCtorIdx n
    if hasNat then mkCtorElim n
    if hasUnit && hasEq && hasHEq then mkNoConfusion n
    if hasUnit && hasProd then mkBelow n
  for n in declNames do
    if hasUnit && hasProd then mkBRecOn n

def updateViewWithFunctorName (view : InductiveView) : InductiveView :=
  let newCtors := view.ctors.map (fun ctor => {ctor with declName := ctor.declName.updatePrefix (addFunctorPostfix ctor.declName.getPrefix)})
  {view with declName := addFunctorPostfix view.declName, ctors := newCtors}

private def elabInductiveViews (vars : Array Expr) (elabs : Array InductiveElabStep1) : TermElabM FinalizeContext := do
  let view0 := elabs[0]!.view
  let ref := view0.ref
  Term.withDeclName view0.declName do withRef ref do
  withExporting (isExporting := !isPrivateName view0.declName) do
    let res ← mkInductiveDecl vars elabs
    -- This might be too coarse, consider reconsidering on construction-by-construction basis
    withoutExporting (when := view0.ctors.any (isPrivateName ·.declName)) do
      mkAuxConstructions (elabs.map (·.view.declName))
      unless view0.isClass do
        mkSizeOfInstances view0.declName
        IndPredBelow.mkBelow view0.declName
        for e in elabs do
          mkInjectiveTheorems e.view.declName
    for e in elabs do
      enableRealizationsForConst e.view.declName
      for ctor in e.view.ctors do
        enableRealizationsForConst ctor.declName
    return res

private def elabFlatInductiveViews (vars : Array Expr) (elabs : Array InductiveElabStep1) : TermElabM Unit := do
  let view0 := elabs[0]!.view
  let ref := view0.ref
  Term.withDeclName view0.declName do withRef ref do
  withExporting (isExporting := !isPrivateName view0.declName) do
    withElaboratedHeaders vars elabs <| mkInductiveDeclCore (fun context =>
     mkFlatInductive context.views context.indFVars context.levelParams context.numVars context.numParams context.indTypes)
    -- This might be too coarse, consider reconsidering on construction-by-construction basis
    withoutExporting (when := view0.ctors.any (isPrivateName ·.declName)) do
      mkAuxConstructions (elabs.map (·.view.declName))
    -- Note that the below applies to the flat inductive
    for e in elabs do
      enableRealizationsForConst e.view.declName

/-- Ensures that there are no conflicts among or between the type and constructor names defined in `elabs`. -/
private def checkNoInductiveNameConflicts (elabs : Array InductiveElabStep1) (isCoinductive : Bool := false) : TermElabM Unit := do
  let throwErrorsAt (init cur : Syntax) (msg : MessageData) : TermElabM Unit := do
    logErrorAt init msg
    throwErrorAt cur msg
  -- Maps names of inductive types to `true` and those of constructors to `false`, along with syntax refs
  let mut uniqueNames : Std.HashMap Name (Bool × Syntax) := {}
  let declString := if isCoinductive then "coinductive predicate" else "inductive type"
  trace[Elab.inductive] "deckString: {declString}"
  for { view, .. } in elabs do
    let typeDeclName := privateToUserName view.declName
    if let some (prevNameIsType, prevRef) := uniqueNames[typeDeclName]? then
      let declKinds := if prevNameIsType then "multiple " ++ declString ++ "s" else "an " ++ declString ++ " and a constructor"
      throwErrorsAt prevRef view.declId m!"Cannot define {declKinds} with the same name `{typeDeclName}`"
    uniqueNames := uniqueNames.insert typeDeclName (true, view.declId)
    for ctor in view.ctors do
      let ctorName := privateToUserName ctor.declName
      if let some (prevNameIsType, prevRef) := uniqueNames[ctorName]? then
        let declKinds := if prevNameIsType then "an {declString} and a constructor" else "multiple constructors"
        throwErrorsAt prevRef ctor.declId m!"Cannot define {declKinds} with the same name `{ctorName}`"
      uniqueNames := uniqueNames.insert ctorName (false, ctor.declId)

private def applyComputedFields (indViews : Array InductiveView) : CommandElabM Unit := do
  if indViews.all (·.computedFields.isEmpty) then return

  let mut computedFields := #[]
  let mut computedFieldDefs := #[]
  for indView@{declName, ..} in indViews do
    for {ref, fieldId, type, matchAlts, modifiers, ..} in indView.computedFields do
      computedFieldDefs := computedFieldDefs.push <| ← do
        let modifiers ← match modifiers with
          | `(Lean.Parser.Command.declModifiersT| $[$doc:docComment]? $[$attrs:attributes]? $[$vis]? $[protected%$protectedTk]? $[noncomputable]?) =>
            `(Lean.Parser.Command.declModifiersT| $[$doc]? $[$attrs]? $[$vis]? $[protected%$protectedTk]? noncomputable)
          | _ => do
            withRef modifiers do logError "Unsupported modifiers for computed field"
            `(Parser.Command.declModifiersT| noncomputable)
        `($(⟨modifiers⟩):declModifiers
          def%$ref $(mkIdent <| `_root_ ++ declName ++ fieldId):ident : $type $matchAlts:matchAlts)
    let computedFieldNames := indView.computedFields.map fun {fieldId, ..} => declName ++ fieldId
    computedFields := computedFields.push (declName, computedFieldNames)
  withScope (fun scope => { scope with
      opts := scope.opts
        |>.set `bootstrap.genMatcherCode false
        |>.set `elaboratingComputedFields true}) <|
    elabCommand <| ← `(mutual $computedFieldDefs* end)

  liftTermElabM do Term.withDeclName indViews[0]!.declName do
    ComputedFields.setComputedFields computedFields

private def applyDerivingHandlers (views : Array InductiveView) : CommandElabM Unit := do
  let mut processed : NameSet := {}
  for view in views do
    for classView in view.derivingClasses do
      let className ← liftCoreM <| classView.getClassName
      unless processed.contains className do
        processed := processed.insert className
        let mut declNames := #[]
        for view in views do
          if view.derivingClasses.any fun classView' => classView'.cls == classView.cls then
            declNames := declNames.push view.declName
        classView.applyHandlers declNames

private def elabInductiveViewsPostprocessing (views : Array InductiveView) (res : FinalizeContext)
     : CommandElabM Unit := do
  let view0 := views[0]!
  let ref := view0.ref
  applyComputedFields views -- NOTE: any generated code before this line is invalid
  liftTermElabM <| withMCtx res.mctx <| withLCtx res.lctx res.localInsts do
    let finalizers ← res.elabs.mapM fun elab' => elab'.prefinalize res.levelParams res.params res.replaceIndFVars
    for view in views do withRef view.declId <|
      Term.applyAttributesAt view.declName view.modifiers.attrs .afterTypeChecking
    for elab' in finalizers do elab'.finalize
  applyDerivingHandlers views
  -- Docstrings are added during postprocessing to allow them to have checked references to
  -- the type and its constructors, but before attributes to enable e.g. `@[inherit_doc X]`
  runTermElabM fun _ => Term.withDeclName view0.declName do withRef ref do
    for view in views do
      withRef view.declId do
        if let some (doc, verso) := view.docString? then
          addDocStringOf verso view.declName view.binders doc
      for ctor in view.ctors do
        withRef ctor.declId do
          if let some (doc, verso) := ctor.modifiers.docString? then
            addDocStringOf verso ctor.declName ctor.binders doc

  runTermElabM fun _ => Term.withDeclName view0.declName do withRef ref do
    for view in views do withRef view.declId <|
      unless (views.any (·.isCoinductive)) do
        Term.applyAttributesAt view.declName view.modifiers.attrs .afterCompilation

  -- Term info is added here so that docstrings are maximally available in the environment for hovers
  runTermElabM fun _ => Term.withDeclName view0.declName <| withRef ref <| addTermInfoViews views

private def elabInductiveViewsPostprocessingCoinductive (views : Array InductiveView)
     : CommandElabM Unit := do
  let view0 := views[0]!
  let ref := view0.ref

  applyDerivingHandlers views
  -- Docstrings are added during postprocessing to allow them to have checked references to
  -- the type and its constructors, but before attributes to enable e.g. `@[inherit_doc X]`
  runTermElabM fun _ => Term.withDeclName view0.declName do withRef ref do
    for view in views do
      withRef view.declId do
        if let some (doc, verso) := view.docString? then
          addDocStringOf verso view.declName view.binders doc
      for ctor in view.ctors do
        withRef ctor.declId do
          if let some (doc, verso) := ctor.modifiers.docString? then
            addDocStringOf verso ctor.declName ctor.binders doc

  runTermElabM fun _ => Term.withDeclName view0.declName do withRef ref do
    for view in views do withRef view.declId <|
      unless (views.any (·.isCoinductive)) do
        Term.applyAttributesAt view.declName view.modifiers.attrs .afterCompilation

  -- Term info is added here so that docstrings are maximally available in the environment for hovers
  runTermElabM fun _ => Term.withDeclName view0.declName <| withRef ref <| addTermInfoViews views

def InductiveViewToCoinductiveElab (e : InductiveElabStep1) : CoinductiveElabData where
  declId := e.view.declId
  declName := e.view.declName
  ref := e.view.ref
  modifiers := e.view.modifiers
  ctorSyntax := e.view.ctors.map (·.ref)
  isGreatest := e.view.isCoinductive

def elabInductives (inductives : Array (Modifiers × Syntax)) : CommandElabM Unit := do
  let elabs ← runTermElabM fun _ =>
      inductives.mapM fun (modifiers, stx) => mkInductiveView modifiers stx

  let isCoinductive := elabs.any (·.view.isCoinductive)

  if isCoinductive then
    runTermElabM fun vars => do
      checkNoInductiveNameConflicts elabs (isCoinductive := true)
      let flatElabs := elabs.map fun e => {e with view := updateViewWithFunctorName e.view}
      flatElabs.forM fun e => checkValidInductiveModifier e.view.modifiers
      elabFlatInductiveViews vars flatElabs
      discard <| flatElabs.mapM fun e => MetaM.run' do mkSumOfProducts e.view.declName
      elabCoinductive (flatElabs.map InductiveViewToCoinductiveElab)
    elabInductiveViewsPostprocessingCoinductive (elabs.map (·.view))
  else
    let res ← runTermElabM fun vars => do
      elabs.forM fun e => checkValidInductiveModifier e.view.modifiers
      checkNoInductiveNameConflicts elabs
      elabInductiveViews vars elabs
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
  if inductives.any (·.1.isMeta) && inductives.any (!·.1.isMeta) then
    throwError "A mix of `meta` and non-`meta` declarations in the same `mutual` block is not supported"
  elabInductives inductives

end Lean.Elab.Command
