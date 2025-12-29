/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Types
public import Lean.Meta.Tactic.Grind.Main
public section
namespace Lean.Meta.Sym
export Grind (ExprPtr Goal)

/--
Information about a single argument position in a function's type signature.

This is used during pattern matching and structural definitional equality tests
to identify arguments that can be skipped or handled specially
(e.g., instance arguments can be synthesized, proof arguments can be inferred).
-/
public structure ProofInstArgInfo where
  /-- `true` if this argument is a proof (its type is a `Prop`). -/
  isProof    : Bool
  /-- `true` if this argument is a type class instance. -/
  isInstance : Bool
  deriving Inhabited

/--
Information about a function symbol. It stores which argument positions are proofs or instances,
enabling optimizations during pattern matching and structural definitional equality tests
such as skipping proof arguments or deferring instance synthesis.
-/
public structure ProofInstInfo where
  /-- Information about each argument position. -/
  argsInfo : Array ProofInstArgInfo
  deriving Inhabited

structure State where
  /--
  Maps expressions to their maximal free variable (by declaration index).

  - `maxFVar[e] = some fvarId` means `fvarId` is the free variable with the largest declaration
    index occurring in `e`.
  - `maxFVar[e] = none` means `e` contains no free variables (but may contain metavariables).

  Recall that if `e` contains a metavariable `?m`, then we assume `e` may contain any free variable
  in the local context associated with `?m`.

  This mapping enables O(1) local context compatibility checks during metavariable assignment.
  Instead of traversing local contexts with `isSubPrefixOf`, we check if the maximal free variable
  in the assigned value is in scope of the metavariable's local context.

  **Note**: We considered using a mapping `PHashMap ExprPtr FVarId`. However, there is a corner
  case that is not supported by this representation. `e` contains a metavariable (with an empty local context),
  and no free variables.
  -/
  maxFVar : PHashMap ExprPtr (Option FVarId) := {}
  proofInstInfo : PHashMap Name (Option ProofInstInfo) := {}

abbrev SymM := ReaderT Grind.Params StateRefT State Grind.GrindM

end Lean.Meta.Sym
