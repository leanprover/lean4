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

unsafe def mkPrecheckAttribute : IO (KeyedDeclsAttribute Precheck) :=
  KeyedDeclsAttribute.init {
    builtinName := `builtinQuotPrecheck,
    name := `quotPrecheck,
    descr    := "Register a double backtick syntax quotation precheck.

  [quotPrecheck k] registers a declaration of type `Lean.Elab.Term.Quotation.Precheck` for the `SyntaxNodeKind` `k`.",
    valueTypeName := ``Precheck
  } `Lean.Elab.Term.Quotation.precheckAttribute
@[builtinInit mkPrecheckAttribute] constant precheckAttribute : KeyedDeclsAttribute Precheck

partial def precheck : Precheck := fun stx => do
  if let p::_ := precheckAttribute.getValues (← getEnv) stx.getKind then
    if ← catchInternalId unsupportedSyntaxExceptionId (do withRef stx <| p stx; true) (fun _ => false) then
      return
  if stx.isAntiquot then
    return
  if !hasIdent stx then
    return  -- we only precheck identifiers, so there is nothing to check here
  if let some stx' ← liftMacroM <| Macro.expandMacro? stx then
    precheck stx'
    return
  throwErrorAt stx "no macro or precheck hook for syntax kind '{stx.getKind}' found{indentD stx}"
where
  hasIdent stx := do
    for stx in stx.topDown do
      if stx.isIdent then
        return true
    return false

def runPrecheck (stx : Syntax) : TermElabM Unit := do
  if hygiene.get (← getOptions) then
    precheck stx |>.run { quotLCtx := {} }

@[builtinQuotPrecheck ident] def precheckIdent : Precheck
  | Syntax.ident info rawVal val preresolved => do
    if !preresolved.isEmpty then
      return
    if let _::_ ← resolveGlobalName val then
      return
    if (← read).quotLCtx.contains val then
      return
    throwError "unknown identifier '{val}'"
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
