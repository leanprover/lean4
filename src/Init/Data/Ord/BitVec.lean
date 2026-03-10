/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Paul Reichert, Robin Arnez
-/
module

prelude
public import Init.Data.Order.Ord
import Init.Data.BitVec.Lemmas

public section

/-!
# Instances for strings.

-/

set_option autoImplicit false
set_option linter.missingDocs true

open Std

namespace BitVec

variable {n : Nat}

instance : TransOrd (BitVec n) :=
  transCmp_compareOfLT { asymm _ _ := BitVec.lt_asymm }
    { trans {_ _ _} := by simpa only [BitVec.not_lt] using flip BitVec.le_trans }

instance : LawfulEqOrd (BitVec n) where
  eq_of_compare h := compareOfLT_eq_eq { asymm _ _ := BitVec.lt_asymm }
    { trichotomous _ _ h₁ h₂ := BitVec.le_antisymm (BitVec.not_lt.mp h₂) (BitVec.not_lt.mp h₁) } |>.mp h

end BitVec
