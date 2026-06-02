/-
Copyright (c) 2026 Lean FRO, LLC. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
import Lean.Elab.Tactic.Grind.DSimprocDSL
import Init.Sym.DSimp.DSimprocDSL
import Lean.Meta.Sym.DSimp.Reduce
import Lean.Meta.Sym.DSimp.DSimproc
import Lean.Meta.Sym.DSimp.EvalGround
namespace Lean.Elab.Tactic.Grind
open Meta Sym.DSimp

-- DSimproc elaborators

@[builtin_sym_dsimproc Lean.Parser.Sym.DSimp.ground]
def elabGround : SymDSimprocElab := fun _ =>
  return evalGround

@[builtin_sym_dsimproc Lean.Parser.Sym.DSimp.zetaDelta]
def elabZetaDeltaAll : SymDSimprocElab := fun _ =>
  return zetaDeltaAll

@[builtin_sym_dsimproc Lean.Parser.Sym.DSimp.zeta]
def elabZeta : SymDSimprocElab := fun _ =>
  return zeta

@[builtin_sym_dsimproc Lean.Parser.Sym.DSimp.beta]
def elabBeta : SymDSimprocElab := fun _ =>
  return beta

@[builtin_sym_dsimproc Lean.Parser.Sym.DSimp.reduceMatch]
def elabReduceMatch : SymDSimprocElab := fun _ =>
  return dsimpMatch

@[builtin_sym_dsimproc Lean.Parser.Sym.DSimp.proj]
def elabProj : SymDSimprocElab := fun _ =>
  return dsimpProj

@[builtin_sym_dsimproc Lean.Parser.Sym.DSimp.none]
def elabNone : SymDSimprocElab := fun _ =>
  return fun _ => return .rfl

@[builtin_sym_dsimproc andThen]
def elabDSimprocAndThen : SymDSimprocElab := fun stx => do
  let `(sym_dsimproc| $left >> $right) := stx | throwUnsupportedSyntax
  let left ← elabSymDSimproc left
  let right ← elabSymDSimproc right
  return left >> right

@[builtin_sym_dsimproc Lean.Parser.Sym.DSimp.orElse]
def elabDSimprocOrElse : SymDSimprocElab := fun stx => do
  let `(sym_dsimproc| $left <|> $right) := stx | throwUnsupportedSyntax
  let left ← elabSymDSimproc left
  let right ← elabSymDSimproc right
  return left <|> right

@[builtin_sym_dsimproc dsimprocParen]
def elabDSimprocParen : SymDSimprocElab := fun stx => do
  let `(sym_dsimproc| ( $proc) ) := stx | throwUnsupportedSyntax
  elabSymDSimproc proc

end Lean.Elab.Tactic.Grind
