/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.SymM
public import Lean.Meta.Sym.Arith.Ring.Types
public section
namespace Lean.Meta.Sym.Arith.Ring

/-- Shared ring state, accessible from both `Sym.simp` and `grind`. -/
builtin_initialize arithRingExt : SymExtension State ← registerSymExtension

end Lean.Meta.Sym.Arith.Ring
