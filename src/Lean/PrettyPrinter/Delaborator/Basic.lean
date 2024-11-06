/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
prelude
import Lean.Elab.Term
import Lean.PrettyPrinter.Delaborator.Options
import Lean.PrettyPrinter.Delaborator.SubExpr
import Lean.PrettyPrinter.Delaborator.TopDownAnalyze

/-!
The delaborator is the first stage of the pretty printer, and the inverse of the
elaborator: it turns fully elaborated `Expr` core terms back into surface-level
`Syntax`, omitting some implicit information again and using higher-level syntax
abstractions like notations where possible. The exact behavior can be customized
using pretty printer options; activating `pp.all` should guarantee that the
delaborator is injective and that re-elaborating the resulting `Syntax`
round-trips.

Pretty printer options can be given not only for the whole term, but also
specific subterms. This is used both when automatically refining pp options
until round-trip and when interactively selecting pp options for a subterm (both
TBD). The association of options to subterms is done by assigning a unique,
synthetic Nat position to each subterm derived from its position in the full
term. This position is added to the corresponding Syntax object so that
elaboration errors and interactions with the pretty printer output can be traced
back to the subterm.

The delaborator is extensible via the `[delab]` attribute.
-/

namespace Lean.PrettyPrinter.Delaborator

open Lean.Meta Lean.SubExpr SubExpr
open Lean.Elab (Info TermInfo Info.ofTermInfo)

structure Context where
  optionsPerPos  : OptionsPerPos
  currNamespace  : Name
  openDecls      : List OpenDecl
  inPattern      : Bool := false -- true when delaborating `match` patterns
  subExpr        : SubExpr
  /-- Current recursion depth during delaboration. Used by the `pp.deepTerms false` option. -/
  depth          : Nat := 0

structure State where
  /-- The number of `delab` steps so far. Used by `pp.maxSteps` to stop delaboration. -/
  steps : Nat := 0
  /-- We attach `Elab.Info` at various locations in the `Syntax` output in order to convey
  its semantics. While the elaborator emits `InfoTree`s, here we have no real text location tree
  to traverse, so we use a flattened map. -/
  infos    : PosMap Info := {}
  /-- See `SubExpr.nextExtraPos`. -/
  holeIter : SubExpr.HoleIterator := {}

-- Exceptions from delaborators are not expected. We use an internal exception to signal whether
-- the delaborator was able to produce a Syntax object.
builtin_initialize delabFailureId : InternalExceptionId ← registerInternalExceptionId `delabFailure

abbrev DelabM := ReaderT Context (StateRefT State MetaM)
abbrev Delab := DelabM Term

instance : Inhabited (DelabM α) where
  default := throw default

@[inline] protected def orElse (d₁ : DelabM α) (d₂ : Unit → DelabM α) : DelabM α := do
  catchInternalId delabFailureId d₁ fun _ => d₂ ()

protected def failure : DelabM α :=
  throw $ Exception.internal delabFailureId

instance : Alternative DelabM where
  orElse  := Delaborator.orElse
  failure := Delaborator.failure

-- HACK: necessary since it would otherwise prefer the instance from MonadExcept
instance {α} : OrElse (DelabM α) := ⟨Delaborator.orElse⟩

-- Low priority instances so `read`/`get`/etc default to the whole `Context`/`State`
instance (priority := low) : MonadReaderOf SubExpr DelabM where
  read := Context.subExpr <$> read

instance (priority := low) : MonadWithReaderOf SubExpr DelabM where
  withReader f x := fun ctx => x { ctx with subExpr := f ctx.subExpr }

instance (priority := low) : MonadStateOf SubExpr.HoleIterator DelabM where
  get         := State.holeIter <$> get
  set iter    := modify fun s => { s with holeIter := iter }
  modifyGet f := modifyGet fun s =>
    let (ret, holeIter') := f s.holeIter
    (ret, { s with holeIter := holeIter' })

-- Macro scopes in the delaborator output are ultimately ignored by the pretty printer,
-- so give a trivial implementation.
instance : MonadQuotation DelabM := {
  getCurrMacroScope   := pure default
  getMainModule       := pure default
  withFreshMacroScope := fun x => x
}

unsafe def mkDelabAttribute : IO (KeyedDeclsAttribute Delab) :=
  KeyedDeclsAttribute.init {
    builtinName := `builtin_delab,
    name := `delab,
    descr    := "Register a delaborator.

  [delab k] registers a declaration of type `Lean.PrettyPrinter.Delaborator.Delab` for the `Lean.Expr`
  constructor `k`. Multiple delaborators for a single constructor are tried in turn until
  the first success. If the term to be delaborated is an application of a constant `c`,
  elaborators for `app.c` are tried first; this is also done for `Expr.const`s (\"nullary applications\")
  to reduce special casing. If the term is an `Expr.mdata` with a single key `k`, `mdata.k`
  is tried first.",
    valueTypeName := `Lean.PrettyPrinter.Delaborator.Delab
    evalKey := fun _ stx => do
      let stx ← Attribute.Builtin.getIdent stx
      let kind := stx.getId
      if (← Elab.getInfoState).enabled && kind.getRoot == `app then
        let c := kind.replacePrefix `app .anonymous
        if (← getEnv).contains c then
          Elab.addConstInfo stx c none
      pure kind
  } `Lean.PrettyPrinter.Delaborator.delabAttribute
@[builtin_init mkDelabAttribute] opaque delabAttribute : KeyedDeclsAttribute Delab

macro "app_delab" id:ident : attr => do
  match ← Macro.resolveGlobalName id.getId with
  | [] => Macro.throwErrorAt id s!"unknown declaration '{id.getId}'"
  | [(c, [])] => `(attr| delab $(mkIdentFrom (canonical := true) id (`app ++ c)))
  | _ => Macro.throwErrorAt id s!"ambiguous declaration '{id.getId}'"

def getExprKind : DelabM Name := do
  let e ← getExpr
  pure $ match e with
  | Expr.bvar _          => `bvar
  | Expr.fvar _          => `fvar
  | Expr.mvar _          => `mvar
  | Expr.sort _          => `sort
  | Expr.const c _       =>
    -- we identify constants as "nullary applications" to reduce special casing
    `app ++ c
  | Expr.app fn _        => match fn.getAppFn with
    | Expr.const c _   => `app ++ c
    | _                => `app
  | Expr.lam _ _ _ _     => `lam
  | Expr.forallE _ _ _ _ => `forallE
  | Expr.letE _ _ _ _ _  => `letE
  | Expr.lit _           => `lit
  | Expr.mdata m _       => match m.entries with
    | [(key, _)] => `mdata ++ key
    | _   => `mdata
  | Expr.proj _ _ _      => `proj

def getOptionsAtCurrPos : DelabM Options := do
  let ctx ← read
  let mut opts ← getOptions
  if let some opts' := ctx.optionsPerPos.find? (← getPos) then
    for (k, v) in opts' do
      opts := opts.insert k v
  return opts

/-- Evaluate option accessor, using subterm-specific options if set. -/
def getPPOption (opt : Options → α) : DelabM α := do
  return opt (← getOptionsAtCurrPos)

def whenPPOption (opt : Options → Bool) (d : Delab) : Delab := do
  let b ← getPPOption opt
  if b then d else failure

def whenNotPPOption (opt : Options → Bool) (d : Delab) : Delab := do
  let b ← getPPOption opt
  if b then failure else d

/-- Set the given option at the current position and execute `x` in this context. -/
def withOptionAtCurrPos (k : Name) (v : DataValue) (x : DelabM α) : DelabM α := do
  let pos ← getPos
  withReader
    (fun ctx =>
      let opts' := ctx.optionsPerPos.find? pos |>.getD {} |>.insert k v
      { ctx with optionsPerPos := ctx.optionsPerPos.insert pos opts' })
    x

def annotatePos (pos : Pos) (stx : Term) : Term :=
  ⟨stx.raw.setInfo (SourceInfo.synthetic ⟨pos⟩ ⟨pos⟩)⟩

def annotateCurPos (stx : Term) : Delab :=
  return annotatePos (← getPos) stx

def addTermInfo (pos : Pos) (stx : Syntax) (e : Expr) (isBinder : Bool := false) : DelabM Unit := do
  let info := Info.ofTermInfo <| ← mkTermInfo stx e isBinder
  modify fun s => { s with infos := s.infos.insert pos info }
where
  mkTermInfo stx e isBinder := return {
    elaborator := `Delab,
    stx := stx,
    lctx := (← getLCtx),
    expectedType? := none,
    expr := e,
    isBinder := isBinder
 }

def addFieldInfo (pos : Pos) (projName fieldName : Name) (stx : Syntax) (val : Expr) : DelabM Unit := do
  let info := Info.ofFieldInfo <| ← mkFieldInfo projName fieldName stx val
  modify fun s => { s with infos := s.infos.insert pos info }
where
  mkFieldInfo projName fieldName stx val := return {
    projName := projName,
    fieldName := fieldName,
    lctx := (← getLCtx),
    val := val,
    stx := stx
  }

/--
Annotates the term with the current expression position and registers `TermInfo`
to associate the term to the current expression.
-/
def annotateTermInfo (stx : Term) : Delab := do
  let stx ← annotateCurPos stx
  addTermInfo (← getPos) stx (← getExpr)
  pure stx

/--
Modifies the delaborator so that it annotates the resulting term with the current expression
position and registers `TermInfo` to associate the term to the current expression.
-/
def withAnnotateTermInfo (d : Delab) : Delab := do
  let stx ← d
  annotateTermInfo stx

/--
Gets an name based on `suggestion` that is unused in the local context.
Erases macro scopes.
If `pp.safeShadowing` is true, then the name is allowed to shadow a name in the local context
if the name does not appear in `body`.

If `preserveName` is false, then returns the name, possibly with fresh macro scopes added.
If `suggestion` has macro scopes then the result does as well.
-/
def getUnusedName (suggestion : Name) (body : Expr) (preserveName : Bool := false) : DelabM Name := do
  let (hasScopes, suggestion) :=
    if suggestion.isAnonymous then
      -- Use a nicer binder name than `[anonymous]`. We probably shouldn't do this in all LocalContext use cases, so do it here.
      (true, `a)
    else
      (suggestion.hasMacroScopes, suggestion.eraseMacroScopes)
  let lctx ← getLCtx
  if !lctx.usesUserName suggestion || (preserveName && !hasScopes) then
    return suggestion
  else if preserveName then
    withFreshMacroScope <| MonadQuotation.addMacroScope suggestion
  else if (← getPPOption getPPSafeShadowing) && !bodyUsesSuggestion lctx suggestion then
    return suggestion
  else
    return lctx.getUnusedName suggestion
where
  bodyUsesSuggestion (lctx : LocalContext) (suggestion' : Name) : Bool :=
    Option.isSome <| body.find? fun
      | Expr.fvar fvarId =>
        match lctx.find? fvarId with
        | none      => false
        | some decl => decl.userName == suggestion'
      | _ => false

/--
Creates an identifier that is annotated with the term `e`, using a fresh position using the `HoleIterator`.
-/
def mkAnnotatedIdent (n : Name) (e : Expr) : DelabM Ident := do
  let pos ← nextExtraPos
  let stx : Syntax := annotatePos pos (mkIdent n)
  addTermInfo pos stx e
  return ⟨stx⟩

/--
Enters the body of the current expression, which must be a lambda or forall.
The binding variable is passed to `d` as `Syntax`, and it is an identifier that has been annotated with the fvar expression
for the variable.

If `preserveName` is `false` (the default), gives the binder an unused name.
Otherwise, it tries to preserve the textual form of the name, preserving whether it is hygienic.
-/
def withBindingBodyUnusedName {α} (d : Syntax → DelabM α) (preserveName := false) : DelabM α := do
  let n ← getUnusedName (← getExpr).bindingName! (← getExpr).bindingBody! (preserveName := preserveName)
  withBindingBody' n (mkAnnotatedIdent n) (d ·)

inductive OmissionReason
  | deep
  | proof
  | maxSteps

def OmissionReason.toString : OmissionReason → String
  | deep => "Term omitted due to its depth (see option `pp.deepTerms`)."
  | proof => "Proof omitted (see option `pp.proofs`)."
  | maxSteps => "Term omitted due to reaching the maximum number of steps allowed for pretty printing this expression (see option `pp.maxSteps`)."

def addOmissionInfo (pos : Pos) (stx : Syntax) (e : Expr) (reason : OmissionReason) : DelabM Unit := do
  let info := Info.ofOmissionInfo <| ← mkOmissionInfo stx e
  modify fun s => { s with infos := s.infos.insert pos info }
where
  mkOmissionInfo stx e := return {
    toTermInfo := ← addTermInfo.mkTermInfo stx e (isBinder := false)
    reason := reason.toString
  }

/--
Runs the delaborator `act` with increased depth.
The depth is used when `pp.deepTerms` is `false` to determine what is a deep term.
See also `Lean.PrettyPrinter.Delaborator.Context.depth`.
-/
def withIncDepth (act : DelabM α) : DelabM α := fun ctx =>
  act { ctx with depth := ctx.depth + 1 }

/--
Returns true if `e` is a "shallow" expression.
Local variables, constants, and other atomic expressions are always shallow.
In general, an expression is considered to be shallow if its depth is at most `threshold`.

Since the implementation uses `Lean.Expr.approxDepth`, the `threshold` is clamped to `[0, 254]`.
-/
def isShallowExpression (threshold : Nat) (e : Expr) : Bool :=
  -- Approximate depth is saturated at 255 for very deep expressions.
  -- Need to clamp to `[0, 254]` so that not every expression is shallow.
  let threshold := min 254 threshold
  e.approxDepth.toNat ≤ threshold

/--
Returns `true` if, at the current depth, we should omit the term and use `⋯` rather than
delaborating it. This function can only return `true` if `pp.deepTerms` is set to `false`.
It also contains a heuristic to allow "shallow terms" to be delaborated, even if they appear deep in
an expression, which prevents terms such as atomic expressions or `OfNat.ofNat` literals from being
delaborated as `⋯`.
-/
def shouldOmitExpr (e : Expr) : DelabM Bool := do
  -- Atomic expressions never get omitted, so we can do an early return here.
  if e.isAtomic then
    return false

  if (← getPPOption getPPDeepTerms) then
    return false

  let depth := (← read).depth
  let depthThreshold ← getPPOption getPPDeepTermsThreshold
  let depthExcess := depth - depthThreshold
  -- This threshold for shallow expressions effectively allows full terms to be pretty printed 25% deeper,
  -- so long as the subterm actually can be fully pretty printed within this extra 25% depth.
  let threshold := depthThreshold/4 - depthExcess

  return depthExcess > 0 && !isShallowExpression threshold e

/--
Returns `true` if the given expression is a proof and should be omitted.
This function only returns `true` if `pp.proofs` is set to `false`.

"Shallow" proofs are not omitted.
The `pp.proofs.threshold` option controls the depth threshold for what constitutes a shallow proof.
See `Lean.PrettyPrinter.Delaborator.isShallowExpression`.
-/
def shouldOmitProof (e : Expr) : DelabM Bool := do
  -- Atomic expressions never get omitted, so we can do an early return here.
  if e.isAtomic then
    return false

  if (← getPPOption getPPProofs) then
    return false

  unless (← try Meta.isProof e catch _ => pure false) do
    return false

  return !isShallowExpression (← getPPOption getPPProofsThreshold) e

/--
Delaborates the current expression as `⋯` and attaches `Elab.OmissionInfo`, which influences how the
subterm omitted by `⋯` is delaborated when hovered over.
-/
def omission (reason : OmissionReason) : Delab := do
  let stx ← `(⋯)
  let stx ← annotateCurPos stx
  addOmissionInfo (← getPos) stx (← getExpr) reason
  pure stx

partial def delabFor : Name → Delab
  | Name.anonymous => failure
  | k              =>
    (do annotateTermInfo (← (delabAttribute.getValues (← getEnv) k).firstM id))
    -- have `app.Option.some` fall back to `app` etc.
    <|> if k.isAtomic then failure else delabFor k.getRoot

partial def delab : Delab := do
  checkSystem "delab"

  if (← get).steps ≥ (← getPPOption getPPMaxSteps) then
    return ← omission .maxSteps
  modify fun s => {s with steps := s.steps + 1}

  let e ← getExpr

  if ← shouldOmitExpr e then
    return ← omission .deep

  if ← shouldOmitProof e then
    let pf ← omission .proof
    if ← getPPOption getPPProofsWithType then
      let stx ← withType delab
      return ← annotateCurPos (← `(($pf : $stx)))
    else
      return pf

  let k ← getExprKind
  let stx ← withIncDepth <| delabFor k <|> (liftM $ show MetaM _ from throwError "don't know how to delaborate '{k}'")
  if ← getPPOption getPPAnalyzeTypeAscriptions <&&> getPPOption getPPAnalysisNeedsType <&&> pure !e.isMData then
    let typeStx ← withType delab
    `(($stx : $typeStx)) >>= annotateCurPos
  else
    return stx

unsafe def mkAppUnexpanderAttribute : IO (KeyedDeclsAttribute Unexpander) :=
  KeyedDeclsAttribute.init {
    name  := `app_unexpander,
    descr := "Register an unexpander for applications of a given constant.

[app_unexpander c] registers a `Lean.PrettyPrinter.Unexpander` for applications of the constant `c`. The unexpander is
passed the result of pre-pretty printing the application *without* implicitly passed arguments. If `pp.explicit` is set
to true or `pp.notation` is set to false, it will not be called at all.",
    valueTypeName := `Lean.PrettyPrinter.Unexpander
    evalKey := fun _ stx => do
      Elab.realizeGlobalConstNoOverloadWithInfo (← Attribute.Builtin.getIdent stx)
  } `Lean.PrettyPrinter.Delaborator.appUnexpanderAttribute
@[builtin_init mkAppUnexpanderAttribute] opaque appUnexpanderAttribute : KeyedDeclsAttribute Unexpander

end Delaborator

open SubExpr (Pos PosMap)
open Delaborator (OptionsPerPos topDownAnalyze DelabM)

def delabCore (e : Expr) (optionsPerPos : OptionsPerPos := {}) (delab : DelabM α) :
  MetaM (α × PosMap Elab.Info) := do
  /- Using `erasePatternAnnotations` here is a bit hackish, but we do it
     `Expr.mdata` affects the delaborator. TODO: should we fix that? -/
  let e ← Meta.erasePatternRefAnnotations e
  trace[PrettyPrinter.delab.input] "{Std.format e}"
  let mut opts ← getOptions
  -- default `pp.proofs` to `true` if `e` is a proof
  if pp.proofs.get? opts == none &&
      -- necessary for `delabConstWithSignature`, and harmless otherwise
      !e.isConst then
    try if ← Meta.isProof e then opts := pp.proofs.set opts true
    catch _ => pure ()
  withOptions (fun _ => opts) do
    let e ← if getPPInstantiateMVars opts then instantiateMVars e else pure e
    let e ← if getPPBeta opts then Core.betaReduce e else pure e
    let optionsPerPos ←
      if !getPPAll opts && getPPAnalyze opts && optionsPerPos.isEmpty then
        topDownAnalyze e
      else pure optionsPerPos
    let (stx, {infos := infos, ..}) ← catchInternalId Delaborator.delabFailureId
        (delab
          { optionsPerPos := optionsPerPos
            currNamespace := (← getCurrNamespace)
            openDecls := (← getOpenDecls)
            subExpr := SubExpr.mkRoot e
            inPattern := opts.getInPattern }
          |>.run { : Delaborator.State })
        (fun _ => unreachable!)
    return (stx, infos)

/-- "Delaborate" the given term into surface-level syntax using the default and given subterm-specific options. -/
def delab (e : Expr) (optionsPerPos : OptionsPerPos := {}) : MetaM Term := do
  let (stx, _) ← delabCore e optionsPerPos Delaborator.delab
  return stx

builtin_initialize
  registerTraceClass `PrettyPrinter.delab
  registerTraceClass `PrettyPrinter.delab.input

end Lean.PrettyPrinter
