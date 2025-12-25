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

structure State where
  maxFVar : PHashMap ExprPtr (Option FVarId) := {}

abbrev SymM := ReaderT Grind.Params StateRefT State Grind.GrindM

end Lean.Meta.Sym
