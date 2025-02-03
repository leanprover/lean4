/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.Array.Lemmas
import Init.Data.List.OfFn

/-!
# Theorems about `Array.ofFn`
-/

namespace Array

@[simp]
theorem ofFn_eq_empty_iff {f : Fin n → α} : ofFn f = #[] ↔ n = 0 := by
  rw [← Array.toList_inj]
  simp

@[simp 500]
theorem mem_ofFn {n} (f : Fin n → α) (a : α) : a ∈ ofFn f ↔ ∃ i, f i = a := by
  constructor
  · intro w
    obtain ⟨i, h, rfl⟩ := getElem_of_mem w
    exact ⟨⟨i, by simpa using h⟩, by simp⟩
  · rintro ⟨i, rfl⟩
    apply mem_of_getElem (i := i) <;> simp

end Array
