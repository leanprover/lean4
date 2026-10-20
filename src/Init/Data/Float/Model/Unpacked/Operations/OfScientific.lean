/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julia M. Himmel
-/
module

prelude
public import Init.Data.Float.Model.Unpacked.Operations.Mul
public import Init.Data.Float.Model.Unpacked.Operations.Div
public import Init.Data.Nat.Bitwise.Lemmas

-- This file is part of the logical model for floats which authors of float libraries
-- need to rely on.
@[expose] public section

namespace Float.Model.UnpackedFloat

/-- Computes `m * 10 ^ e`. -/
def ofScientific (spec : Format) (m : Nat) (e : Int) : UnpackedFloat :=
  if hm : m = 0 then
    .zero .positive
  -- Safety check to avoid computing huge powers of ten
  else if e > 2 ^ spec.exponentBits then
    .infinity .positive
  -- Safety check to avoid computing huge powers of ten
  else if e < -((2 ^ spec.exponentBits : Int) + m.log2) then
    .zero .positive
  else if 0 ≤ e then
    mul spec (.finite .positive (m <<< spec.mantissaBits) (-spec.mantissaBits) (by simpa [Nat.pos_iff_ne_zero]))
      (.finite .positive (10 ^ e.toNat) 0 (Nat.pow_pos (by decide)))
  else
    div spec (.finite .positive m 0 (Nat.pos_iff_ne_zero.2 hm))
      (.finite .positive (10 ^ (-e).toNat) 0 (Nat.pow_pos (by decide)))

end Float.Model.UnpackedFloat
