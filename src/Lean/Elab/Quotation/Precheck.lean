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

structure Precheck.Context where
  quotLCtx : NameSet

abbrev PrecheckM := ReaderT Precheck.Context TermElabM
abbrev Precheck  := Syntax → PrecheckM Unit

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
    p stx
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

def runPrecheck (stx : Syntax) : TermElabM Unit :=
  precheck stx |>.run { quotLCtx := {} }

end Lean.Elab.Term.Quotation
