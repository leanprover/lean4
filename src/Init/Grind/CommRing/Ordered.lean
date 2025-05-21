/-
Copyright (c) 2025 Lean FRO, LLC. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
import Init.Grind.CommRing.Basic

namespace Lean.Grind

class Ring.IsOrdered (R : Type u) [Ring R] [Preorder R] extends IntModule.IsOrdered R where
  /-- In a strict ordered semiring, we have `0 < 1`. -/
  zero_lt_one : 0 < 1
  /-- In a strict ordered semiring, we can multiply an inequality `a < b` on the left
  by a positive element `0 < c` to obtain `c * a < c * b`. -/
  protected mul_lt_mul_of_pos_left : ∀ a b c : R, a < b → 0 < c → c * a < c * b
  /-- In a strict ordered semiring, we can multiply an inequality `a < b` on the right
  by a positive element `0 < c` to obtain `a * c < b * c`. -/
  protected mul_lt_mul_of_pos_right : ∀ a b c : R, a < b → 0 < c → a * c < b * c

namespace Ring.IsOrdered

end Ring.IsOrdered

end Lean.Grind
