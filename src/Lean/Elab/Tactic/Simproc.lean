/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Simp.Simproc
import Lean.Elab.Binders
import Lean.Elab.SyntheticMVars
import Lean.Elab.Term
import Lean.Elab.Command

namespace Lean.Elab

open Lean Meta Simp

def elabPattern (stx : Syntax) : MetaM Expr := do
  let go : TermElabM Expr := do
    let pattern ← Term.elabTerm stx none
    Term.synthesizeSyntheticMVars
    return pattern
  go.run'

def checkSimprocType (declName : Name) : CoreM Unit := do
  let decl ← getConstInfo declName
  match decl.type with
  | .const ``Simproc _ => pure ()
  | _ => throwError "unexpected type at '{declName}', 'Simproc' expected"

namespace Command

@[builtin_command_elab Lean.Parser.simprocPattern] def elabSimprocPattern : CommandElab := fun stx => do
  let `(simproc_pattern% $pattern => $declName) := stx | throwUnsupportedSyntax
  let declName := declName.getId
  liftTermElabM do
    checkSimprocType declName
    let pattern ← elabPattern pattern
    let keys ← DiscrTree.mkPath pattern simpDtConfig
    registerSimproc declName keys

end Command

builtin_initialize
  registerBuiltinAttribute {
    ref             := by exact decl_name%
    name            := `simprocAttr
    descr           := "Simplification procedure"
    erase           := eraseSimprocAttr
    add             := fun declName stx attrKind => do
      let go : MetaM Unit := do
        let post := if stx[1].isNone then true else stx[1][0].getKind == ``Lean.Parser.Tactic.simpPost
        addSimprocAttr declName attrKind post
      go.run' {}
    applicationTime := AttributeApplicationTime.afterCompilation
  }

end Lean.Elab
