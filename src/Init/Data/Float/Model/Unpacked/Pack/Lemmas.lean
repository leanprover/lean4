/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julia M. Himmel
-/
module

prelude
public import Init.Data.Float.Model.Unpacked.Pack.Basic
public import Init.Data.Float.Model.Format.Valid

-- This file is part of the logical model for floats which authors of float libraries
-- need to rely on.
@[expose] public section

/-!
These are only the lemmas required to write down the operations on `Float.Model` and
`Float32.Model`. There will not be any additional lemmas; see the docstring of `UnpackedFloat` for
more details.
-/

namespace Float.Model.UnpackedFloat

@[simp]
theorem unpackMantissa_packComponents {spec : Format} {sign exponent mantissa} :
    unpackMantissa (packComponents spec sign exponent mantissa) = mantissa := by
  ext i hi
  simp [unpackMantissa, packComponents, BitVec.getLsbD_eq_getElem, BitVec.getLsbD_append, hi]

@[simp]
theorem unpackExponent_packComponents {spec : Format} {sign exponent mantissa} :
    unpackExponent (packComponents spec sign exponent mantissa) = exponent := by
  ext i hi
  simp [unpackExponent, packComponents, BitVec.getLsbD_eq_getElem, BitVec.getLsbD_append, hi]

@[simp]
theorem valid_pack {spec : Format} {f : UnpackedFloat} : spec.Valid (pack spec f) := by
  refine ⟨?_⟩
  fun_cases pack with
  | case1 => simp
  | case2 s => simp [packedInfinity]
  | case3 s => simp [packedZero]
  | case4 s m e hm biasedExponent h => simp [packedInfinity]
  | case5 s m e hm actualMantissaBits biasedExponent h₁ h₂ =>
    suffices biasedExponent % 2 ^ spec.exponentBits ≠ 2 ^ spec.exponentBits - 1 by
      simp [BitVec.neg_one_eq_allOnes, ← BitVec.toNat_inj, this]
    suffices biasedExponent < 2 ^ spec.exponentBits - 1 by
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    omega
  | case6 s m e hm actualMantissaBits biasedExponent h₁ h₂ =>
    simp [Nat.pos_iff_ne_zero.1 spec.he]

end Float.Model.UnpackedFloat
