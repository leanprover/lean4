/-
Copyright (c) 2025 Lean FRO, LLC. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
prelude

public import Init.Grind.Ordered.Module
import Init.Classical
import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Init.Omega

public section

namespace Lean.Grind

instance : AddRightCancel Nat where
  add_right_cancel _ _ _ := Nat.add_right_cancel

instance : ExistsAddOfLT Nat where
  exists_add_of_le {a b} h := ⟨b - a, by omega⟩

end Lean.Grind
