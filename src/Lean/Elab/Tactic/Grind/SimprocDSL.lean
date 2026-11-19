/-
Copyright (c) 2026 Lean FRO, LLC. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Elab.Tactic.Grind.Basic
public import Lean.Meta.Sym.Simp.Discharger
import Init.Sym.Simp.SimprocDSL
public section
namespace Lean.Elab.Tactic.Grind
open Meta Sym.Simp

/-- Elaboration function for `sym_simproc` syntax. -/
abbrev SymSimprocElab := Syntax → GrindTacticM Simproc

/-- Elaboration function for `sym_discharger` syntax. -/
abbrev SymDischargerElab := Syntax → GrindTacticM Discharger

unsafe builtin_initialize symSimprocElabAttribute : KeyedDeclsAttribute SymSimprocElab ←
  mkElabAttribute SymSimprocElab `builtin_sym_simproc `sym_simproc
    `Lean.Parser.Sym.Simp `Lean.Elab.Tactic.Grind.SymSimprocElab "sym_simproc"

unsafe builtin_initialize symDischargerElabAttribute : KeyedDeclsAttribute SymDischargerElab ←
  mkElabAttribute SymDischargerElab `builtin_sym_discharger `sym_discharger
    `Lean.Parser.Sym.Simp `Lean.Elab.Tactic.Grind.SymDischargerElab "sym_discharger"

/-- Elaborate a `sym_simproc` syntax node into a `Simproc`. -/
partial def elabSymSimproc (stx : Syntax) : GrindTacticM Simproc := do
  let elabFns := symSimprocElabAttribute.getEntries (← getEnv) stx.getKind
  for elabFn in elabFns do
    try
      return (← elabFn.value stx)
    catch ex =>
      match ex with
      | .internal id _ =>
        if id == unsupportedSyntaxExceptionId then continue
        else throw ex
      | _ => throw ex
  throwErrorAt stx "unsupported sym_simproc syntax `{stx.getKind}`"

/-- Elaborate a `sym_discharger` syntax node into a `Discharger`. -/
def elabSymDischarger (stx : Syntax) : GrindTacticM Discharger := do
  let elabFns := symDischargerElabAttribute.getEntries (← getEnv) stx.getKind
  for elabFn in elabFns do
    try
      return (← elabFn.value stx)
    catch ex =>
      match ex with
      | .internal id _ =>
        if id == unsupportedSyntaxExceptionId then continue
        else throw ex
      | _ => throw ex
  throwErrorAt stx "unsupported sym_discharger syntax `{stx.getKind}`"

end Lean.Elab.Tactic.Grind
