/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/

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

import Lean.KeyedDeclsAttribute
import Lean.ProjFns
import Lean.Syntax
import Lean.Meta.Match
import Lean.Elab.Term

namespace Lean

register_builtin_option pp.all : Bool := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) display coercions, implicit parameters, proof terms, fully qualified names, universes, " ++
              "and disable beta reduction and notations during pretty printing"
}
register_builtin_option pp.notation : Bool := {
  defValue := true
  group    := "pp"
  descr    := "(pretty printer) disable/enable notation (infix, mixfix, postfix operators and unicode characters)"
}
register_builtin_option pp.coercions : Bool := {
  defValue := true
  group    := "pp"
  descr    := "(pretty printer) hide coercion applications"
}
register_builtin_option pp.universes : Bool := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) display universes"
}
register_builtin_option pp.full_names : Bool := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) display fully qualified names"
}
register_builtin_option pp.private_names : Bool := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) display internal names assigned to private declarations"
}
register_builtin_option pp.binder_types : Bool := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) display types of lambda and Pi parameters"
}
register_builtin_option pp.structure_instances : Bool := {
  defValue := true
  group    := "pp"
  -- TODO: implement second part
  descr    := "(pretty printer) display structure instances using the '{ fieldName := fieldValue, ... }' notation " ++
              "or '⟨fieldValue, ... ⟩' if structure is tagged with [pp_using_anonymous_constructor] attribute"
}
register_builtin_option pp.structure_projections : Bool := {
  defValue := true
  group    := "pp"
  descr    := "(pretty printer) display structure projections using field notation"
}
register_builtin_option pp.explicit : Bool := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) display implicit arguments"
}
register_builtin_option pp.structure_instance_type : Bool := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) display type of structure instances"
}
register_builtin_option pp.safe_shadowing  : Bool := {
  defValue := true
  group    := "pp"
  descr    := "(pretty printer) allow variable shadowing if there is no collision"
}
register_builtin_option pp.proofs : Bool := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) if set to false, replace proofs appearing as an argument to a function with a placeholder"
}
register_builtin_option pp.proofs.withType : Bool := {
  defValue := true
  group    := "pp"
  descr    := "(pretty printer) when eliding a proof (see `pp.proofs`), show its type instead"
}

-- TODO:
/-
register_builtin_option g_pp_max_depth : Nat := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) maximum expression depth, after that it will use ellipsis"
}
register_builtin_option g_pp_max_steps : Nat := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) maximum number of visited expressions, after that it will use ellipsis"
}
register_builtin_option g_pp_locals_full_names : Bool := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) show full names of locals"
}
register_builtin_option g_pp_beta : Bool := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) apply beta-reduction when pretty printing"
}
register_builtin_option g_pp_goal_compact : Bool := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) try to display goal in a single line when possible"
}
register_builtin_option g_pp_goal_max_hyps : Nat := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) maximum number of hypotheses to be displayed"
}
register_builtin_option g_pp_instantiate_mvars : Bool := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) instantiate assigned metavariables before pretty printing terms and goals"
}
register_builtin_option g_pp_annotations : Bool := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) display internal annotations (for debugging purposes only)"
}
register_builtin_option g_pp_compact_let : Bool := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) minimal indentation at `let`-declarations"
}
-/

def getPPAll (o : Options) : Bool := o.get `pp.all false
def getPPBinderTypes (o : Options) : Bool := o.get `pp.binder_types true
def getPPCoercions (o : Options) : Bool := o.get `pp.coercions (!getPPAll o)
def getPPExplicit (o : Options) : Bool := o.get `pp.explicit (getPPAll o)
def getPPNotation (o : Options) : Bool := o.get `pp.notation (!getPPAll o)
def getPPStructureProjections (o : Options) : Bool := o.get `pp.structure_projections (!getPPAll o)
def getPPStructureInstances (o : Options) : Bool := o.get `pp.structure_instances (!getPPAll o)
def getPPStructureInstanceType (o : Options) : Bool := o.get `pp.structure_instance_type (getPPAll o)
def getPPUniverses (o : Options) : Bool := o.get `pp.universes (getPPAll o)
def getPPFullNames (o : Options) : Bool := o.get `pp.full_names (getPPAll o)
def getPPPrivateNames (o : Options) : Bool := o.get `pp.private_names (getPPAll o)
def getPPUnicode (o : Options) : Bool := o.get `pp.unicode true
def getPPSafeShadowing (o : Options) : Bool := o.get `pp.safe_shadowing true
def getPPProofs (o : Options) : Bool := o.get pp.proofs.name (getPPAll o)
def getPPProofsWithType (o : Options) : Bool := o.get pp.proofs.withType.name true

/-- Associate pretty printer options to a specific subterm using a synthetic position. -/
abbrev OptionsPerPos := Std.RBMap Nat Options compare

namespace PrettyPrinter
namespace Delaborator
open Lean.Meta

structure Context where
  -- In contrast to other systems like the elaborator, we do not pass the current term explicitly as a
  -- parameter, but store it in the monad so that we can keep it in sync with `pos`.
  expr           : Expr
  pos            : Nat := 1
  defaultOptions : Options
  optionsPerPos  : OptionsPerPos
  currNamespace  : Name
  openDecls      : List OpenDecl
  inPattern      : Bool := false -- true whe delaborating `match` patterns

-- Exceptions from delaborators are not expected. We use an internal exception to signal whether
-- the delaborator was able to produce a Syntax object.
builtin_initialize delabFailureId : InternalExceptionId ← registerInternalExceptionId `delabFailure

abbrev DelabM := ReaderT Context MetaM
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

def getExpr : DelabM Expr := do
  let ctx ← read
  pure ctx.expr

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

/-- Evaluate option accessor, using subterm-specific options if set. -/
def getPPOption (opt : Options → Bool) : DelabM Bool := do
  let ctx ← read
  let mut opts := ctx.defaultOptions
  if let some opts' ← ctx.optionsPerPos.find? ctx.pos then
    for (k, v) in opts' do
      opts := opts.insert k v
  return opt opts

def whenPPOption (opt : Options → Bool) (d : Delab) : Delab := do
  let b ← getPPOption opt
  if b then d else failure

def whenNotPPOption (opt : Options → Bool) (d : Delab) : Delab := do
  let b ← getPPOption opt
  if b then failure else d

/--
Descend into `child`, the `childIdx`-th subterm of the current term, and update position.

Because `childIdx < 3` in the case of `Expr`, we can injectively map a path
`childIdxs` to a natural number by computing the value of the 3-ary representation
`1 :: childIdxs`, since n-ary representations without leading zeros are unique.
Note that `pos` is initialized to `1` (case `childIdxs == []`).
-/
def descend {α} (child : Expr) (childIdx : Nat) (d : DelabM α) : DelabM α :=
  withReader (fun cfg => { cfg with expr := child, pos := cfg.pos * 3 + childIdx }) d

def withAppFn {α} (d : DelabM α) : DelabM α := do
  let Expr.app fn _ _ ← getExpr | unreachable!
  descend fn 0 d

def withAppArg {α} (d : DelabM α) : DelabM α := do
  let Expr.app _ arg _ ← getExpr | unreachable!
  descend arg 1 d

partial def withAppFnArgs {α} : DelabM α → (α → DelabM α) → DelabM α
  | fnD, argD => do
    let Expr.app fn arg _ ← getExpr | fnD
    let a ← withAppFn (withAppFnArgs fnD argD)
    withAppArg (argD a)

def withBindingDomain {α} (d : DelabM α) : DelabM α := do
  let e ← getExpr
  descend e.bindingDomain! 0 d

def withBindingBody {α} (n : Name) (d : DelabM α) : DelabM α := do
  let e ← getExpr
  withLocalDecl n e.binderInfo e.bindingDomain! fun fvar =>
    let b := e.bindingBody!.instantiate1 fvar
    descend b 1 d

def withProj {α} (d : DelabM α) : DelabM α := do
  let Expr.proj _ _ e _ ← getExpr | unreachable!
  descend e 0 d

def withMDataExpr {α} (d : DelabM α) : DelabM α := do
  let Expr.mdata _ e _ ← getExpr | unreachable!
  -- do not change position so that options on an mdata are automatically forwarded to the child
  withReader ({ · with expr := e }) d

partial def annotatePos (pos : Nat) : Syntax → Syntax
  | stx@(Syntax.ident _ _ _ _)                   => stx.setInfo (SourceInfo.synthetic pos pos)
  -- app => annotate function
  | stx@(Syntax.node `Lean.Parser.Term.app args) => stx.modifyArg 0 (annotatePos pos)
  -- otherwise, annotate first direct child token if any
  | stx => match stx.getArgs.findIdx? Syntax.isAtom with
    | some idx => stx.modifyArg idx (Syntax.setInfo (SourceInfo.synthetic pos pos))
    | none     => stx

def annotateCurPos (stx : Syntax) : Delab := do
  let ctx ← read
  pure $ annotatePos ctx.pos stx

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
    let env ← getEnv
    (match (delabAttribute.ext.getState env).table.find? k with
     | some delabs => delabs.firstM id >>= annotateCurPos
     | none        => failure) <|>
      -- have `app.Option.some` fall back to `app` etc.
      delabFor k.getRoot

partial def delab : Delab := do
  unless (← getPPOption getPPProofs) do
    let e ← getExpr
    -- no need to hide atomic proofs
    unless e.isAtomic do
      try
        let ty ← Meta.inferType (← getExpr)
        if ← Meta.isProp ty then
          if ← getPPOption getPPProofsWithType then
            return ← ``((_ : $(← descend ty 0 delab)))
          else
            return ← ``(_)
      catch _ => pure ()
  let k ← getExprKind
  delabFor k <|> (liftM $ show MetaM Syntax from throwError "don't know how to delaborate '{k}'")

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

/-- "Delaborate" the given term into surface-level syntax using the default and given subterm-specific options. -/
def delab (currNamespace : Name) (openDecls : List OpenDecl) (e : Expr) (optionsPerPos : OptionsPerPos := {}) : MetaM Syntax := do
  trace[PrettyPrinter.delab.input] "{fmt e}"
  let mut opts ← MonadOptions.getOptions
  -- default `pp.proofs` to `true` if `e` is a proof
  if pp.proofs.get? opts == none then
    try
      let ty ← Meta.inferType e
      if ← Meta.isProp ty then
        opts := pp.proofs.set opts true
    catch _ => pure ()
  catchInternalId Delaborator.delabFailureId
    (Delaborator.delab.run { expr := e, defaultOptions := opts, optionsPerPos := optionsPerPos, currNamespace := currNamespace, openDecls := openDecls })
    (fun _ => unreachable!)

builtin_initialize registerTraceClass `PrettyPrinter.delab

end PrettyPrinter
end Lean
