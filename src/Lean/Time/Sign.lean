/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Lean.Time.Bounded

namespace Lean
set_option linter.all true

/--
A `Sign` is a type that can have three values -1, 0 and 1 that represents the sign of a value.
-/
def Sign := Bounded.LE (-1) 1

namespace Sign

/--
Gets the `Sign` out of a integer.
-/
@[inline]
def ofInt (val : Int) : Sign := by
  refine ⟨val.sign, ?_⟩
  simp [Int.sign]
  split <;> simp

@[inline]
def apply (sign : Sign) (val : Int) : Int :=
  val * sign.val
