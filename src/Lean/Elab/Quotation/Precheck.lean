/-
Copyright (c) 2021 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/

import Lean.KeyedDeclsAttribute
import Lean.Parser.Command  -- for `precheckedQuot`
import Lean.Elab.Term
import Lean.Elab.Quotation.Util

namespace Lean.Elab.Term.Quotation
open Lean.Elab.Term
open Lean.Parser.Term

structure Precheck.Context where
  quotLCtx : NameSet

abbrev PrecheckM := ReaderT Precheck.Context TermElabM
abbrev Precheck  := Syntax → PrecheckM Unit

protected def withNewLocal (l : Name) (x : PrecheckM α) : PrecheckM α :=
  withReader (fun ctx => { ctx with quotLCtx := ctx.quotLCtx.insert l }) x

protected def withNewLocals (ls : Array Name) (x : PrecheckM α) : PrecheckM α :=
  withReader (fun ctx => { ctx with quotLCtx := ls.foldl NameSet.insert ctx.quotLCtx }) x

register_builtin_option quotPrecheck : Bool := {
  defValue := true
  descr    := "Enable eager name analysis on notations in order to find unbound identifiers early.
Note that type-sensitive syntax (\"elaborators\") needs special support for this kind of check, so it might need to be turned off when using such syntax."
}

register_builtin_option quotPrecheck.allowSectionVars : Bool := {
  defValue := false
  descr    := "Allow occurrences of section variables in checked quotations, it is useful when declaring local notation."
}

unsafe def mkPrecheckAttribute : IO (KeyedDeclsAttribute Precheck) :=
  KeyedDeclsAttribute.init {
    builtinName := `builtin_quot_precheck,
    name := `quot_precheck,
    descr    := "Register a double backtick syntax quotation pre-check.

[quot_precheck k] registers a declaration of type `Lean.Elab.Term.Quotation.Precheck` for the `SyntaxNodeKind` `k`.
It should implement eager name analysis on the passed syntax by throwing an exception on unbound identifiers,
and calling `precheck` recursively on nested terms, potentially with an extended local context (`withNewLocal`).
Macros without registered precheck hook are unfolded, and identifier-less syntax is ultimately assumed to be well-formed.",
    valueTypeName := ``Precheck
  } `Lean.Elab.Term.Quotation.precheckAttribute
@[builtin_init mkPrecheckAttribute] opaque precheckAttribute : KeyedDeclsAttribute Precheck

partial def precheck : Precheck := fun stx => do
  if let p::_ := precheckAttribute.getValues (← getEnv) stx.getKind then
    if ← catchInternalId unsupportedSyntaxExceptionId (do withRef stx <| p stx; pure true) (fun _ => pure false) then
      return
  if stx.isAnyAntiquot then
    return
  if !hasQuotedIdent stx then
    return  -- we only precheck identifiers, so there is nothing to check here
  if let some stx' ← liftMacroM <| expandMacro? stx then
    precheck stx'
    return
  throwErrorAt stx "no macro or `[quot_precheck]` instance for syntax kind '{stx.getKind}' found{indentD stx}
This means we cannot eagerly check your notation/quotation for unbound identifiers; you can use `set_option quotPrecheck false` to disable this check."
where
  hasQuotedIdent
    | Syntax.ident .. => true
    | stx =>
      if stx.isAnyAntiquot then
        false
      else
        stx.getArgs.any hasQuotedIdent

def runPrecheck (stx : Syntax) : TermElabM Unit := do
  let opts ← getOptions
  if quotPrecheck.get opts && hygiene.get opts then
    precheck stx |>.run { quotLCtx := {} }

private def isSectionVariable (e : Expr) : TermElabM Bool := do
  return (← read).sectionFVars.any fun _ v => e == v

@[builtin_quot_precheck ident] def precheckIdent : Precheck := fun stx =>
  match stx with
  | Syntax.ident _    _      val preresolved => do
    if !preresolved.isEmpty then
      return
    /- The precheck currently ignores field notation.
       For example: the following notation is accepted although `foo` is not a valid field name for a `Nat` value.
       ```
       def x := 0
       notation "x++" => x.foo
       ```
    -/
    if let _::_ ← resolveGlobalNameWithInfos stx val then
      return
    if (← read).quotLCtx.contains val then
      return
    let rs ← try resolveName stx val [] [] catch _ => pure []
    for (e, _) in rs do
      match e with
      | Expr.fvar _      .. =>
        if quotPrecheck.allowSectionVars.get (← getOptions) && (← isSectionVariable e) then
          return
      | _ => pure ()
    throwError "unknown identifier '{val}' at quotation precheck; you can use `set_option quotPrecheck false` to disable this check."
  | _ => throwUnsupportedSyntax

@[builtin_quot_precheck Lean.Parser.Term.app] def precheckApp : Precheck
  | `($f $args*) => do
    precheck f
    for arg in args.raw do
      match arg with
      | `(argument| ($_ := $e)) => precheck e
      | `(argument| ..)         => pure ()
      | `(argument| $e:term)    => precheck e
  | _ => throwUnsupportedSyntax

@[builtin_quot_precheck Lean.Parser.Term.typeAscription] def precheckTypeAscription : Precheck
  | `(($e : $type)) => do
    precheck e
    precheck type
  | `(($e :)) => precheck e
  | _ => throwUnsupportedSyntax

@[builtin_quot_precheck Lean.Parser.Term.explicit] def precheckExplicit : Precheck
  | `(@ $id) => do
    precheck id
  | _ => throwUnsupportedSyntax

@[builtin_quot_precheck choice] def precheckChoice : Precheck := fun stx => do
  let checks ← stx.getArgs.mapM (_root_.observing ∘ precheck)
  let fails := checks.zip stx.getArgs |>.filterMap fun
    | (.error e, stx) => some m!"{stx}\n{e.toMessageData}"
    | _               => none
  unless fails.isEmpty do
    throwErrorAt stx "ambiguous notation with at least one interpretation that failed quotation precheck, possible interpretations {indentD (MessageData.joinSep fails.toList m!"\n\n")}"

@[builtin_term_elab precheckedQuot] def elabPrecheckedQuot : TermElab := fun stx expectedType? => do
  let singleQuot := stx[1]
  runPrecheck singleQuot.getQuotContent
  adaptExpander (fun _ => pure singleQuot) stx expectedType?

section ExpressionTree

@[builtin_quot_precheck Lean.Parser.Term.binrel] def precheckBinrel : Precheck
  | `(binrel% $f $a $b) => do precheck f; precheck a; precheck b
  | _ => throwUnsupportedSyntax

@[builtin_quot_precheck Lean.Parser.Term.binrel_no_prop] def precheckBinrelNoProp : Precheck
  | `(binrel_no_prop% $f $a $b) => do precheck f; precheck a; precheck b
  | _ => throwUnsupportedSyntax

@[builtin_quot_precheck Lean.Parser.Term.binop] def precheckBinop : Precheck
  | `(binop% $f $a $b) => do precheck f; precheck a; precheck b
  | _ => throwUnsupportedSyntax

@[builtin_quot_precheck Lean.Parser.Term.binop_lazy] def precheckBinopLazy : Precheck
  | `(binop_lazy% $f $a $b) => do precheck f; precheck a; precheck b
  | _ => throwUnsupportedSyntax

@[builtin_quot_precheck Lean.Parser.Term.leftact] def precheckLeftact : Precheck
  | `(leftact% $f $a $b) => do precheck f; precheck a; precheck b
  | _ => throwUnsupportedSyntax

@[builtin_quot_precheck Lean.Parser.Term.rightact] def precheckRightact : Precheck
  | `(rightact% $f $a $b) => do precheck f; precheck a; precheck b
  | _ => throwUnsupportedSyntax

@[builtin_quot_precheck Lean.Parser.Term.unop] def precheckUnop : Precheck
  | `(unop% $f $a) => do precheck f; precheck a
  | _ => throwUnsupportedSyntax

end ExpressionTree

end Lean.Elab.Term.Quotation
