/-
Copyright (c) 2026 Lean FRO, LLC. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Elab.Tactic.Grind.Basic
public import Lean.Meta.Sym.DSimp
import Init.Sym.DSimp.DSimprocDSL
public section
namespace Lean.Elab.Tactic.Grind
open Meta Sym.DSimp

/-- Elaboration function for `sym_dsimproc` syntax. -/
abbrev SymDSimprocElab := Syntax → GrindTacticM DSimproc

unsafe builtin_initialize symDSimprocElabAttribute : KeyedDeclsAttribute SymDSimprocElab ←
  mkElabAttribute SymDSimprocElab `builtin_sym_dsimproc `sym_dsimproc
    `Lean.Parser.Sym.DSimp `Lean.Elab.Tactic.Grind.SymDSimprocElab "sym_dsimproc"

/-- Elaborate a `sym_dsimproc` syntax node into a `DSimproc`. -/
partial def elabSymDSimproc (stx : Syntax) : GrindTacticM DSimproc := do
  let elabFns := symDSimprocElabAttribute.getEntries (← getEnv) stx.getKind
  for elabFn in elabFns do
    try
      return (← elabFn.value stx)
    catch ex =>
      match ex with
      | .internal id _ =>
        if id == unsupportedSyntaxExceptionId then continue
        else throw ex
      | _ => throw ex
  throwErrorAt stx "unsupported sym_dsimproc syntax `{stx.getKind}`"

end Lean.Elab.Tactic.Grind
