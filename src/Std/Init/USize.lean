/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Init.Data.Fin.Lemmas
import Std.Init.Nat

namespace USize

theorem toNat_and {a b : USize} : (a &&& b).toNat = a.toNat &&& b.toNat := by
  change (a.toNat &&& b.toNat) % _ = _
  rw [Nat.mod_eq_of_lt]
  have : a.toNat < size := a.1.2
  exact Nat.lt_of_le_of_lt Nat.and_le_left this

theorem toNat_sub_le {a b : USize} (h : b ≤ a) : (a - b).toNat = a.toNat - b.toNat :=
  Fin.coe_sub_iff_le.2 h

theorem toNat_lt' {a : USize} : a.toNat < USize.size :=
  a.1.2

end USize
