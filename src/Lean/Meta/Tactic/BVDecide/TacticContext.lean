/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Meta.Tactic.BVDecide.Attr

public section

/-!
This module contains the logic around writing proofs of UNSAT, using LRAT proofs, as meta code.
-/

namespace Lean.Meta.Tactic.BVDecide

open Elab.Term
open Elab.Tactic.BVDecide

/--
The context for the `bv_decide` tactic.
-/
structure TacticContext where
  exprDef : Name
  certDef : Name
  reflectionDef : Name
  solver : System.FilePath
  lratPath : System.FilePath
  config : BVDecideConfig
  /--
  The types that the structure and enum analysis is restricted to, as provided by the `types`
  clause. If this is `none` the analysis discovers the relevant types on its own.
  -/
  restrictedTypes : Option (Array Name) := none

def TacticContext.new (lratPath : System.FilePath) (config : BVDecideConfig)
    (restrictedTypes : Option (Array Name) := none) : TermElabM TacticContext := do
  let exprDef ← Lean.Elab.Term.mkAuxName `_expr_def
  let certDef ← Lean.Elab.Term.mkAuxName `_cert_def
  let reflectionDef ← Lean.Elab.Term.mkAuxName `_reflection_def
  let solver ← determineSolver
  trace[Meta.Tactic.sat] m!"Using SAT solver at '{solver}'"
  return {
    exprDef,
    certDef,
    reflectionDef,
    solver,
    lratPath,
    config,
    restrictedTypes
  }
where
  determineSolver : CoreM System.FilePath := do
    let opts ← getOptions
    let option := sat.solver.get opts
    if option == "" then
      let cadicalPath := (← IO.appPath).parent.get! / "cadical" |>.withExtension System.FilePath.exeExtension
      if ← cadicalPath.pathExists then
        return cadicalPath
      else
        return "cadical"
    else
      return option

end Lean.Meta.Tactic.BVDecide
