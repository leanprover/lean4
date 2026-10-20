/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julia M. Himmel
-/
module

prelude
public import Init.Data.Fin.Basic
import Init.Data.Order.Lemmas
import Init.Data.Nat.Order
import Init.Data.Nat.MinMax

namespace Fin

public instance : Min (Fin n) where
  min a b := ⟨min a b, by simpa [Std.min_lt_iff] using Or.inl a.isLt⟩

public instance : Max (Fin n) where
  max a b := ⟨max a b, by simpa [Std.max_lt_iff] using ⟨a.isLt, b.isLt⟩⟩

@[simp] public theorem val_min (a b : Fin n) : (min a b).val = min a.val b.val := rfl
@[simp] public theorem val_max (a b : Fin n) : (max a b).val = max a.val b.val := rfl

end Fin
