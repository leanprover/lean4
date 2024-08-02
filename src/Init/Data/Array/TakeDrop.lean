/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Init.Data.Array.Lemmas
import Init.Data.List.Nat.TakeDrop

namespace Array

theorem exists_of_uset (self : Array α) (i d h) :
    ∃ l₁ l₂, self.data = l₁ ++ self[i] :: l₂ ∧ List.length l₁ = i.toNat ∧
      (self.uset i d h).data = l₁ ++ d :: l₂ := by
  simpa [Array.getElem_eq_data_getElem] using List.exists_of_set _

end Array
