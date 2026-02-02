/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Pattern
public import Lean.Meta.DiscrTree
import Lean.Meta.Sym.Simp.DiscrTree
public section
namespace Lean.Meta.Sym.Simp

/--
A simplification theorem for the structural simplifier.

Contains both the theorem expression and a precomputed pattern for efficient unification
during rewriting.
-/
structure Theorem where
  /-- The theorem expression, typically `Expr.const declName` for a named theorem. -/
  expr    : Expr
  /-- Precomputed pattern extracted from the theorem's type for efficient matching. -/
  pattern : Pattern
  /-- Right-hand side of the equation. -/
  rhs     : Expr

instance : BEq Theorem where
  beq thm₁ thm₂ := thm₁.expr == thm₂.expr

/-- Collection of simplification theorems available to the simplifier. -/
structure Theorems where
  thms : DiscrTree Theorem := {}

def Theorems.insert (thms : Theorems) (thm : Theorem) : Theorems :=
  { thms with thms := insertPattern thms.thms thm.pattern thm }

def Theorems.getMatch (thms : Theorems) (e : Expr) : Array Theorem :=
  Sym.getMatch thms.thms e

def Theorems.getMatchWithExtra (thms : Theorems) (e : Expr) : Array (Theorem × Nat) :=
  Sym.getMatchWithExtra thms.thms e

def mkTheoremFromDecl (declName : Name) : MetaM Theorem := do
  let (pattern, rhs) ← mkEqPatternFromDecl declName
  return { expr := mkConst declName, pattern, rhs }

end Lean.Meta.Sym.Simp
