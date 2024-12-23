/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Core

namespace Lean.Grind

/-- A helper gadget for annotating nested proofs in goals. -/
def nestedProof (p : Prop) (h : p) : p := h

end Lean.Grind
