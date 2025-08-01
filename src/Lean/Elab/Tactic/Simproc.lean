/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Init.Simproc
public import Lean.ReservedNameAction
public import Lean.Meta.Tactic.Simp.Simproc
public import Lean.Elab.Binders
public import Lean.Elab.SyntheticMVars
public import Lean.Elab.Term
public import Lean.Elab.Command

public section

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
  withSimpGlobalConfig <| DiscrTree.mkPath pattern

def checkSimprocType (declName : Name) : CoreM Bool := do
  let decl ← getConstInfo declName
  match decl.type with
  | .const ``Simproc _ => pure false
  | .const ``DSimproc _ => pure true
  | _ => throwError "Unexpected type for simproc pattern: Expected `{.ofConstName ``Simproc}` or \
          `{.ofConstName ``DSimproc}`, but `{declName}` has type{indentExpr decl.type}"

namespace Command

@[builtin_command_elab Lean.Parser.simprocPattern] def elabSimprocPattern : CommandElab := fun stx => do
  let `(simproc_pattern% $pattern => $declName) := stx | throwUnsupportedSyntax
  liftTermElabM do
    let declName ← realizeGlobalConstNoOverload declName
    discard <| checkSimprocType declName
    let keys ← elabSimprocKeys pattern
    registerSimproc declName keys

@[builtin_command_elab Lean.Parser.simprocPatternBuiltin] def elabSimprocPatternBuiltin : CommandElab := fun stx => do
  let `(builtin_simproc_pattern% $pattern => $declName) := stx | throwUnsupportedSyntax
  liftTermElabM do
    let declName ← realizeGlobalConstNoOverload declName
    let dsimp ← checkSimprocType declName
    let keys ← elabSimprocKeys pattern
    let registerProcName := if dsimp then ``registerBuiltinDSimproc else ``registerBuiltinSimproc
    let val := mkAppN (mkConst registerProcName) #[toExpr declName, toExpr keys, mkConst declName]
    let initDeclName ← mkFreshUserName (declName ++ `declare)
    declareBuiltin initDeclName val

end Command

end Lean.Elab
