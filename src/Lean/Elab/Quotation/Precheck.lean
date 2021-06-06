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
    builtinName := `builtinQuotPrecheck,
    name := `quotPrecheck,
    descr    := "Register a double backtick syntax quotation pre-check.

[quotPrecheck k] registers a declaration of type `Lean.Elab.Term.Quotation.Precheck` for the `SyntaxNodeKind` `k`.
It should implement eager name analysis on the passed syntax by throwing an exception on unbound identifiers,
and calling `precheck` recursively on nested terms, potentially with an extended local context (`withNewLocal`).
Macros without registered precheck hook are unfolded, and identifier-less syntax is ultimately assumed to be well-formed.",
    valueTypeName := ``Precheck
  } `Lean.Elab.Term.Quotation.precheckAttribute
@[builtinInit mkPrecheckAttribute] constant precheckAttribute : KeyedDeclsAttribute Precheck

partial def precheck : Precheck := fun stx => do
  if let p::_ := precheckAttribute.getValues (← getEnv) stx.getKind then
    if ← catchInternalId unsupportedSyntaxExceptionId (do withRef stx <| p stx; true) (fun _ => false) then
      return
  if stx.isAnyAntiquot then
    return
  if !hasQuotedIdent stx then
    return  -- we only precheck identifiers, so there is nothing to check here
  if let some stx' ← liftMacroM <| expandMacro? stx then
    precheck stx'
    return
  throwErrorAt stx "no macro or `[quotPrecheck]` instance for syntax kind '{stx.getKind}' found{indentD stx}
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

@[builtinQuotPrecheck ident] def precheckIdent : Precheck := fun stx =>
  match stx with
  | Syntax.ident info rawVal val preresolved => do
    if !preresolved.isEmpty then
      return
    /- The precheck currently ignores field notation.
       For example: the following notation is accepted although `foo` is not a valid field name for a `Nat` value.
       ```
       def x := 0
       notation "x++" => x.foo
       ```
    -/
    if let _::_ ← resolveGlobalName val then
      return
    if (← read).quotLCtx.contains val then
      return
    let rs ← try resolveName stx val [] [] catch _ => pure []
    for (e, _) in rs do
      match e with
      | Expr.fvar fvarId .. =>
        if quotPrecheck.allowSectionVars.get (← getOptions) && (← isSectionVariable e) then
          return
      | _ => pure ()
    throwError "unknown identifier '{val}' at quotation precheck; you can use `set_option quotPrecheck false` to disable this check."
  | _ => throwUnsupportedSyntax

@[builtinQuotPrecheck Lean.Parser.Term.app] def precheckApp : Precheck
  | `($f $args*) => do
    precheck f
    for arg in args do
      match arg with
      | `(argument| ($n := $e)) => precheck e
      | `(argument| $e:term)    => precheck e
      | `(argument| ..)         => pure ()
      | _ => throwUnsupportedSyntax
  | _ => throwUnsupportedSyntax

@[builtinQuotPrecheck Lean.Parser.Term.paren] def precheckParen : Precheck
  | `(())           => pure ()
  | `(($e : $type)) => do
    precheck e
    precheck type
  | `(($e))         => precheck e
  | `(($e, $es,*))  => do
    precheck e
    es.getElems.forM precheck
  | _ => throwUnsupportedSyntax

@[builtinTermElab precheckedQuot] def elabPrecheckedQuot : TermElab := fun stx expectedType? => do
  let singleQuot := stx[1]
  runPrecheck singleQuot.getQuotContent
  adaptExpander (fun _ => singleQuot) stx expectedType?

end Lean.Elab.Term.Quotation
