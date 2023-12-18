/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
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

structure State where
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
  set iter    := modify fun ⟨infos, _⟩ => ⟨infos, iter⟩
  modifyGet f := modifyGet fun ⟨infos, iter⟩ => let (ret, iter') := f iter; (ret, ⟨infos, iter'⟩)

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
def getPPOption (opt : Options → Bool) : DelabM Bool := do
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

def getUnusedName (suggestion : Name) (body : Expr) : DelabM Name := do
  -- Use a nicer binder name than `[anonymous]`. We probably shouldn't do this in all LocalContext use cases, so do it here.
  let suggestion := if suggestion.isAnonymous then `a else suggestion
  -- We use this small hack to convert identifiers created using `mkAuxFunDiscr` to simple names
  let suggestion := suggestion.eraseMacroScopes
  let lctx ← getLCtx
  if !lctx.usesUserName suggestion then
    return suggestion
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

def withBindingBodyUnusedName {α} (d : Syntax → DelabM α) : DelabM α := do
  let n ← getUnusedName (← getExpr).bindingName! (← getExpr).bindingBody!
  let stxN ← annotateCurPos (mkIdent n)
  withBindingBody n $ d stxN

@[inline] def liftMetaM {α} (x : MetaM α) : DelabM α :=
  liftM x

def addTermInfo (pos : Pos) (stx : Syntax) (e : Expr) (isBinder : Bool := false) : DelabM Unit := do
  let info ← mkTermInfo stx e isBinder
  modify fun s => { s with infos := s.infos.insert pos info }
where
  mkTermInfo stx e isBinder := return Info.ofTermInfo {
    elaborator := `Delab,
    stx := stx,
    lctx := (← getLCtx),
    expectedType? := none,
    expr := e,
    isBinder := isBinder
 }

def addFieldInfo (pos : Pos) (projName fieldName : Name) (stx : Syntax) (val : Expr) : DelabM Unit := do
  let info ← mkFieldInfo projName fieldName stx val
  modify fun s => { s with infos := s.infos.insert pos info }
where
  mkFieldInfo projName fieldName stx val := return Info.ofFieldInfo {
    projName := projName,
    fieldName := fieldName,
    lctx := (← getLCtx),
    val := val,
    stx := stx
  }

def annotateTermInfo (stx : Term) : Delab := do
  let stx ← annotateCurPos stx
  addTermInfo (← getPos) stx (← getExpr)
  pure stx

partial def delabFor : Name → Delab
  | Name.anonymous => failure
  | k              =>
    (do annotateTermInfo (← (delabAttribute.getValues (← getEnv) k).firstM id))
    -- have `app.Option.some` fall back to `app` etc.
    <|> if k.isAtomic then failure else delabFor k.getRoot

partial def delab : Delab := do
  checkSystem "delab"
  let e ← getExpr

  -- no need to hide atomic proofs
  if ← pure !e.isAtomic <&&> pure !(← getPPOption getPPProofs) <&&> (try Meta.isProof e catch _ => pure false) then
    if ← getPPOption getPPProofsWithType then
      let stx ← withType delab
      return ← annotateTermInfo (← `((_ : $stx)))
    else
      return ← annotateTermInfo (← ``(_))
  let k ← getExprKind
  let stx ← delabFor k <|> (liftM $ show MetaM _ from throwError "don't know how to delaborate '{k}'")
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
      Elab.resolveGlobalConstNoOverloadWithInfo (← Attribute.Builtin.getIdent stx)
  } `Lean.PrettyPrinter.Delaborator.appUnexpanderAttribute
@[builtin_init mkAppUnexpanderAttribute] opaque appUnexpanderAttribute : KeyedDeclsAttribute Unexpander

end Delaborator

open SubExpr (Pos PosMap)
open Delaborator (OptionsPerPos topDownAnalyze)

def delabCore (e : Expr) (optionsPerPos : OptionsPerPos := {}) (delab := Delaborator.delab) : MetaM (Term × PosMap Elab.Info) := do
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
  let (stx, _) ← delabCore e optionsPerPos
  return stx

builtin_initialize registerTraceClass `PrettyPrinter.delab

end Lean.PrettyPrinter
