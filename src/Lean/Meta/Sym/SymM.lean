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
  maxFVar : PHashMap ExprPtr (Option FVarId) := {}
  proofInstInfo : PHashMap Name (Option ProofInstInfo) := {}

abbrev SymM := ReaderT Grind.Params StateRefT State Grind.GrindM

end Lean.Meta.Sym
