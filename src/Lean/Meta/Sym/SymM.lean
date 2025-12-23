/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Types
namespace Lean.Meta.Sym
export Grind (ExprPtr Goal)

structure State where
  maxFVar : PHashMap ExprPtr Expr := {}

public abbrev SymM := StateRefT State Grind.GrindM

end Lean.Meta.Sym
