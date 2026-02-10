/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.Elab.Term.TermElabM
import Lean.Elab.Do.Basic
import Lean.Elab.Do.Legacy

public section

namespace Lean.Elab.Term

register_builtin_option backward.do.legacy : Bool := {
  defValue := true
  descr    := "Use the legacy `do` elaborator instead of the new, extensible implementation."
}

private def toDoElem (newKind : SyntaxNodeKind) : Macro := fun stx => do
  let stx := stx.setKind newKind
  withRef stx `(do $(⟨stx⟩):doElem)

@[builtin_macro Lean.Parser.Term.termFor]
def expandTermFor : Macro := toDoElem ``Parser.Term.doFor

@[builtin_macro Lean.Parser.Term.termTry]
def expandTermTry : Macro := toDoElem ``Parser.Term.doTry

@[builtin_macro Lean.Parser.Term.termUnless]
def expandTermUnless : Macro := toDoElem ``Parser.Term.doUnless

@[builtin_macro Lean.Parser.Term.termReturn]
def expandTermReturn : Macro := toDoElem ``Parser.Term.doReturn

@[builtin_term_elab «do»]
def elabDo : TermElab := fun stx expectedType? => do
  if backward.do.legacy.get (← getOptions) then
    Term.Do.elabDo stx expectedType?
  else
    Elab.Do.elabDo stx expectedType?

@[builtin_term_elab liftMethod] def elabTermLiftMethod : TermElab := fun stx ty => do
  if backward.do.legacy.get (← getOptions) then
    Term.elabLiftMethod stx ty
  else
    throwError "Not implemented yet"
