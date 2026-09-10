/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julia M. Himmel
-/
module

prelude
public import Init.Data.Order.PackageFactories
import Init.Data.Int.Order
import Init.Data.Int.Compare
import Init.Data.Order.Lemmas

open Std

namespace Int

public instance : LinearOrderPackage Int := .ofLE _ {
  beq_iff_le_and_ge a b := by simpa using Int.le_antisymm_iff
}

end Int
