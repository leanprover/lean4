/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
import Lean.KeyedDeclsAttribute
import Lean.ProjFns
import Lean.Syntax
import Lean.Meta.Match
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

open Lean.Meta SubExpr

structure Context where
  defaultOptions : Options
  optionsPerPos  : OptionsPerPos
  currNamespace  : Name
  openDecls      : List OpenDecl
  inPattern      : Bool := false -- true whe delaborating `match` patterns

-- Exceptions from delaborators are not expected. We use an internal exception to signal whether
-- the delaborator was able to produce a Syntax object.
builtin_initialize delabFailureId : InternalExceptionId ← registerInternalExceptionId `delabFailure

abbrev DelabM := ReaderT Context (ReaderT SubExpr MetaM)
abbrev Delab := DelabM Syntax

instance {α} : Inhabited (DelabM α) where
  default := throw arbitrary

@[inline] protected def orElse {α} (d₁ d₂ : DelabM α) : DelabM α := do
catchInternalId delabFailureId d₁ (fun _ => d₂)
protected def failure {α} : DelabM α := throw $ Exception.internal delabFailureId
instance : Alternative DelabM := {
  orElse  := Delaborator.orElse,
  failure := Delaborator.failure
}
-- HACK: necessary since it would otherwise prefer the instance from MonadExcept
instance {α} : OrElse (DelabM α) := ⟨Delaborator.orElse⟩

-- Macro scopes in the delaborator output are ultimately ignored by the pretty printer,
-- so give a trivial implementation.
instance : MonadQuotation DelabM := {
  getCurrMacroScope   := pure arbitrary,
  getMainModule       := pure arbitrary,
  withFreshMacroScope := fun x => x
}

unsafe def mkDelabAttribute : IO (KeyedDeclsAttribute Delab) :=
  KeyedDeclsAttribute.init {
    builtinName := `builtinDelab,
    name := `delab,
    descr    := "Register a delaborator.

  [delab k] registers a declaration of type `Lean.PrettyPrinter.Delaborator.Delab` for the `Lean.Expr`
  constructor `k`. Multiple delaborators for a single constructor are tried in turn until
  the first success. If the term to be delaborated is an application of a constant `c`,
  elaborators for `app.c` are tried first; this is also done for `Expr.const`s (\"nullary applications\")
  to reduce special casing. If the term is an `Expr.mdata` with a single key `k`, `mdata.k`
  is tried first.",
    valueTypeName := `Lean.PrettyPrinter.Delaborator.Delab
  } `Lean.PrettyPrinter.Delaborator.delabAttribute
@[builtinInit mkDelabAttribute] constant delabAttribute : KeyedDeclsAttribute Delab

def getExprKind : DelabM Name := do
  let e ← getExpr
  pure $ match e with
  | Expr.bvar _ _        => `bvar
  | Expr.fvar _ _        => `fvar
  | Expr.mvar _ _        => `mvar
  | Expr.sort _ _        => `sort
  | Expr.const c _ _     =>
    -- we identify constants as "nullary applications" to reduce special casing
    `app ++ c
  | Expr.app fn _ _      => match fn.getAppFn with
    | Expr.const c _ _ => `app ++ c
    | _                => `app
  | Expr.lam _ _ _ _     => `lam
  | Expr.forallE _ _ _ _ => `forallE
  | Expr.letE _ _ _ _ _  => `letE
  | Expr.lit _ _         => `lit
  | Expr.mdata m _ _     => match m.entries with
    | [(key, _)] => `mdata ++ key
    | _   => `mdata
  | Expr.proj _ _ _ _    => `proj

def getOptionsAtCurrPos : DelabM Options := do
  let ctx ← read
  let mut opts := ctx.defaultOptions
  if let some opts' ← ctx.optionsPerPos.find? (← getPos) then
    for (k, v) in opts' do
      opts := opts.insert k v
  opts

/-- Evaluate option accessor, using subterm-specific options if set. -/
def getPPOption (opt : Options → Bool) : DelabM Bool := do
  return opt (← getOptionsAtCurrPos)

def whenPPOption (opt : Options → Bool) (d : Delab) : Delab := do
  let b ← getPPOption opt
  if b then d else failure

def whenNotPPOption (opt : Options → Bool) (d : Delab) : Delab := do
  let b ← getPPOption opt
  if b then failure else d

partial def annotatePos (pos : Nat) : Syntax → Syntax
  | stx@(Syntax.ident _ _ _ _)                   => stx.setInfo (SourceInfo.synthetic pos pos)
  -- app => annotate function
  | stx@(Syntax.node `Lean.Parser.Term.app args) => stx.modifyArg 0 (annotatePos pos)
  -- otherwise, annotate first direct child token if any
  | stx => match stx.getArgs.findIdx? Syntax.isAtom with
    | some idx => stx.modifyArg idx (Syntax.setInfo (SourceInfo.synthetic pos pos))
    | none     => stx

def annotateCurPos (stx : Syntax) : Delab := do
  annotatePos (← getPos) stx

def getUnusedName (suggestion : Name) (body : Expr) : DelabM Name := do
  -- Use a nicer binder name than `[anonymous]`. We probably shouldn't do this in all LocalContext use cases, so do it here.
  let suggestion := if suggestion.isAnonymous then `a else suggestion;
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
      | Expr.fvar fvarId _ =>
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

partial def delabFor : Name → Delab
  | Name.anonymous => failure
  | k              => do
    (delabAttribute.getValues (← getEnv) k).firstM id >>= annotateCurPos <|>
      -- have `app.Option.some` fall back to `app` etc.
      delabFor k.getRoot

partial def delab : Delab := do
  checkMaxHeartbeats "delab"
  let e ← getExpr

  -- no need to hide atomic proofs
  if ← !e.isAtomic <&&> !(← getPPOption getPPProofs) <&&> (try Meta.isProof e catch ex => false) then
    if ← getPPOption getPPProofsWithType then
      let stx ← withType delab
      return ← ``((_ : $stx))
    else
      return ← ``(_)
  let k ← getExprKind
  let stx ← delabFor k <|> (liftM $ show MetaM Syntax from throwError "don't know how to delaborate '{k}'")
  if ← getPPOption getPPAnalyzeTypeAscriptions <&&> getPPOption getPPAnalysisNeedsType <&&> !e.isMData then
    let typeStx ← withType delab
    `(($stx:term : $typeStx:term)) >>= annotateCurPos
  else stx

unsafe def mkAppUnexpanderAttribute : IO (KeyedDeclsAttribute Unexpander) :=
  KeyedDeclsAttribute.init {
    name := `appUnexpander,
    descr := "Register an unexpander for applications of a given constant.

[appUnexpander c] registers a `Lean.PrettyPrinter.Unexpander` for applications of the constant `c`. The unexpander is
passed the result of pre-pretty printing the application *without* implicitly passed arguments. If `pp.explicit` is set
to true or `pp.notation` is set to false, it will not be called at all.",
    valueTypeName := `Lean.PrettyPrinter.Unexpander
  } `Lean.PrettyPrinter.Delaborator.appUnexpanderAttribute
@[builtinInit mkAppUnexpanderAttribute] constant appUnexpanderAttribute : KeyedDeclsAttribute Unexpander

end Delaborator

open Delaborator (OptionsPerPos topDownAnalyze)

/-- "Delaborate" the given term into surface-level syntax using the default and given subterm-specific options. -/
def delab (currNamespace : Name) (openDecls : List OpenDecl) (e : Expr) (optionsPerPos : OptionsPerPos := {}) : MetaM Syntax := do
  trace[PrettyPrinter.delab.input] "{Std.format e}"
  let mut opts ← MonadOptions.getOptions
  -- default `pp.proofs` to `true` if `e` is a proof
  if pp.proofs.get? opts == none then
    try if ← Meta.isProof e then opts := pp.proofs.set opts true
    catch _ => pure ()
  let e ← if getPPInstantiateMVars opts then ← Meta.instantiateMVars e else e
  let optionsPerPos ←
    if !getPPAll opts && getPPAnalyze opts && optionsPerPos.isEmpty then
      withTheReader Core.Context (fun ctx => { ctx with options := opts }) do topDownAnalyze e
    else optionsPerPos
  catchInternalId Delaborator.delabFailureId
    (Delaborator.delab.run { defaultOptions := opts, optionsPerPos := optionsPerPos, currNamespace := currNamespace, openDecls := openDecls } (Delaborator.SubExpr.mkRoot e))
    (fun _ => unreachable!)

builtin_initialize registerTraceClass `PrettyPrinter.delab

end Lean.PrettyPrinter
