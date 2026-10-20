/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julia M. Himmel
-/
module

prelude
public import Init.Data.Float.Model.Unpacked.Pack.Basic

-- This file is part of the logical model for floats which authors of float libraries
-- need to rely on.
@[expose] public section

namespace Float.Model

open UnpackedFloat

/--
Predicate asserting that the bit representation of a float is valid according to the given
format. By 'valid' we mean that `NaN` is encoded using the canonical `NaN`.
-/
structure Format.Valid (spec : Format) (b : BitVec spec.numBits) : Prop where
  /-- If the bit vector encodes a `NaN`, then it is the canonical `NaN`. -/
  eq_packedNaN : unpackExponent b = (-1#_) → unpackMantissa b ≠ 0#_ → b = packedNaN spec

end Float.Model
