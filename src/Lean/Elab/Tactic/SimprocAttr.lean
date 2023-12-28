/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Simp.Simproc
import Lean.Elab.Binders
import Lean.Elab.SyntheticMVars
import Lean.Elab.Term

namespace Lean.Elab

open Lean Meta Simp

def elabPattern (stx : Syntax) : MetaM Expr := do
  let go : TermElabM Expr := do
    Term.withAutoBoundImplicit <| Term.elabBinders #[] fun xs => do
      let pattern ← Term.elabTerm stx none
      Term.synthesizeSyntheticMVars
      let (_, _, pattern) ← lambdaMetaTelescope (← mkLambdaFVars xs pattern)
      return pattern
  go.run'

def checkSimprocType (declName : Name) : MetaM Unit := do
  let decl ← getConstInfo declName
  match decl.type with
  | .const ``Simproc _ => pure ()
  | _ => throwError "unexpected type at '{declName}', 'Simproc' expected"

builtin_initialize
  registerBuiltinAttribute {
    ref             := by exact decl_name%
    name            := `simproc
    descr           := "Simplification procedure"
    erase           := eraseSimprocAttr
    add             := fun declName stx attrKind => do
      let go : MetaM Unit := do
        let post := if stx[1].isNone then true else stx[1][0].getKind == ``Lean.Parser.Tactic.simpPost
        let prio ← getAttrParamOptPrio stx[2]
        let pattern ← elabPattern stx[3]
        checkSimprocType declName
        addSimprocAttr declName attrKind post prio pattern
      go.run' {}
    applicationTime := AttributeApplicationTime.afterCompilation
  }

end Lean.Elab
