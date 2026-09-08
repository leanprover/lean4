/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julia M. Himmel
-/
module

prelude
public import Init.Data.Nat.Order
public import Init.Data.Nat.Compare
public import Init.Data.Order.PackageFactories
import Init.Data.Order.Lemmas

open Std

namespace Nat

public instance : LinearOrderPackage Nat := .ofLE _ {
  beq_iff_le_and_ge a b := by simpa using Nat.le_antisymm_iff
}

end Nat
