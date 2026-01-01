/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.SymM
public import Lean.Meta.Sym.Pattern
public section
namespace Lean.Meta.Sym.Simp

/-- Configuration options for the structural simplifier. -/
structure Config where
  /-- If `true`, unfold let-bindings (zeta reduction) during simplification. -/
  zetaDelta : Bool := true
  -- **TODO**: many are still missing

/-- The result of simplifying some expression `e`. -/
structure Result where
  /-- The simplified version of `e` -/
  expr           : Expr
  /-- A proof that `e = expr`, where the simplified expression is on the RHS.
  If `none`, the proof is assumed to be `refl`. -/
  proof?         : Option Expr := none

/--
A simplification theorem for the structural simplifier.

Contains both the theorem expression and a precomputed pattern for efficient unification
during rewriting.
-/
structure Theorem where
  /-- The theorem expression, typically `Expr.const declName` for a named theorem. -/
  expr      : Expr
  /-- Precomputed pattern extracted from the theorem's type for efficient matching. -/
  pattern   : Pattern

/-- Collection of simplification theorems available to the simplifier. -/
structure Theorems where
  /-- **TODO**: No indexing for now. We will add a structural discrimination tree later. -/
  thms : Array Theorem := #[]

/-- Read-only context for the simplifier. -/
structure Context where
  /-- Available simplification theorems. -/
  thms   : Theorems := {}
  /-- Simplifier configuration options. -/
  config : Config := {}
  /-- Size of the local context when simplification started.
  Used to determine which free variables were introduced during simplification. -/
  initialLCtxSize : Nat

/-- Cache mapping expressions (by pointer equality) to their simplified results. -/
abbrev Cache := PHashMap ExprPtr Result

/-- Mutable state for the simplifier. -/
structure State where
  /-- Cache of previously simplified expressions to avoid redundant work. -/
  cache : Cache := {}

/-- Monad for the structural simplifier, layered on top of `SymM`. -/
abbrev SimpM := ReaderT Context StateRefT State SymM

/-- Runs a `SimpM` computation with the given theorems and configuration. -/
abbrev SimpM.run (x : SimpM α) (thms : Theorems := {}) (config : Config := {}) : SymM α := do
  let initialLCtxSize := (← getLCtx).decls.size
  x { initialLCtxSize, thms, config } |>.run' {}

end Lean.Meta.Sym.Simp
