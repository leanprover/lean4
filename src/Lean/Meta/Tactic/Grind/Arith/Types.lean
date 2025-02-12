/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Arith.Offset.Types

namespace Lean.Meta.Grind.Arith

/-- State for the arithmetic procedures. -/
structure State where
  offset : Offset.State := {}
  deriving Inhabited

end Lean.Meta.Grind.Arith
