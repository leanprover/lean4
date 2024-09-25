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
    ∃ l₁ l₂, self.toList = l₁ ++ self[i] :: l₂ ∧ List.length l₁ = i.toNat ∧
      (self.uset i d h).toList = l₁ ++ d :: l₂ := by
  simpa only [ugetElem_eq_getElem, getElem_eq_getElem_toList, uset, toList_set] using
    List.exists_of_set _

end Array
