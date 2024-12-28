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

set_option pp.proofs true

theorem nestedProof_congr (p q : Prop) (h : p = q) (hp : p) (hq : q) : HEq (nestedProof p hp) (nestedProof q hq) := by
  subst h; apply HEq.refl

end Lean.Grind
