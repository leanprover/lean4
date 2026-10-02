/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julia M. Himmel
-/
module

prelude
public import Init.Data.Order.PackageFactories
import Init.Data.Nat.Order
import Init.Data.Nat.Compare

open Std

namespace Nat

-- This should really be a `LinearOrderPackage Nat` instance. However, this would trigger
-- #15082 in a grind test, so we just provide `LawfulOrderBEq` for now.
public instance : LawfulOrderBEq Nat where
  beq_iff_le_and_ge a b := by simpa using Nat.le_antisymm_iff

end Nat
