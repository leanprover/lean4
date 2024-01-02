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

def elabSimprocPattern (stx : Syntax) : MetaM Expr := do
  let go : TermElabM Expr := do
    let pattern ← Term.elabTerm stx none
    Term.synthesizeSyntheticMVars
    return pattern
  go.run'

def elabSimprocKeys (stx : Syntax) : MetaM (Array Meta.SimpTheoremKey) := do
  let pattern ← elabSimprocPattern stx
  DiscrTree.mkPath pattern simpDtConfig

def checkSimprocType (declName : Name) : CoreM Unit := do
  let decl ← getConstInfo declName
  match decl.type with
  | .const ``Simproc _ => pure ()
  | _ => throwError "unexpected type at '{declName}', 'Simproc' expected"

namespace Command

@[builtin_command_elab Lean.Parser.simprocPattern] def elabSimprocPattern : CommandElab := fun stx => do
  let `(simproc_pattern% $pattern => $declName) := stx | throwUnsupportedSyntax
  let declName ← resolveGlobalConstNoOverload declName
  liftTermElabM do
    checkSimprocType declName
    let keys ← elabSimprocKeys pattern
    registerSimproc declName keys

@[builtin_command_elab Lean.Parser.simprocPatternBuiltin] def elabSimprocPatternBuiltin : CommandElab := fun stx => do
  let `(builtin_simproc_pattern% $pattern => $declName) := stx | throwUnsupportedSyntax
  let declName ← resolveGlobalConstNoOverload declName
  liftTermElabM do
    checkSimprocType declName
    let keys ← elabSimprocKeys pattern
    let val := mkAppN (mkConst ``registerBuiltinSimproc) #[toExpr declName, toExpr keys, mkConst declName]
    let initDeclName ← mkFreshUserName (declName ++ `declare)
    declareBuiltin initDeclName val

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

builtin_initialize
  registerBuiltinAttribute {
    ref             := by exact decl_name%
    name            := `simprocBuiltinAttr
    descr           := "Builtin simplification procedure"
    erase           := eraseSimprocAttr
    add             := fun declName stx _ => do
      let go : MetaM Unit := do
        let post := if stx[1].isNone then true else stx[1][0].getKind == ``Lean.Parser.Tactic.simpPost
        let val := mkAppN (mkConst ``addSimprocBuiltinAttr) #[toExpr declName, toExpr post, mkConst declName]
        let initDeclName ← mkFreshUserName (declName ++ `declare)
        declareBuiltin initDeclName val
      go.run' {}
    applicationTime := AttributeApplicationTime.afterCompilation
  }

end Lean.Elab
