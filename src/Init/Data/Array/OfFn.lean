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

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace Array

@[simp] theorem ofFn_zero {f : Fin 0 → α} : ofFn f = #[] := by
  simp [ofFn, ofFn.go]

theorem ofFn_succ {f : Fin (n+1) → α} :
    ofFn f = (ofFn (fun (i : Fin n) => f i.castSucc)).push (f ⟨n, by omega⟩) := by
  ext i h₁ h₂
  · simp
  · simp [getElem_push]
    split <;> rename_i h₃
    · rfl
    · congr
      simp at h₁ h₂
      omega

@[simp] theorem _root_.List.toArray_ofFn {f : Fin n → α} : (List.ofFn f).toArray = Array.ofFn f := by
  ext <;> simp

@[simp] theorem toList_ofFn {f : Fin n → α} : (Array.ofFn f).toList = List.ofFn f := by
  apply List.ext_getElem <;> simp

@[simp]
theorem ofFn_eq_empty_iff {f : Fin n → α} : ofFn f = #[] ↔ n = 0 := by
  rw [← Array.toList_inj]
  simp

@[simp 500]
theorem mem_ofFn {n} {f : Fin n → α} {a : α} : a ∈ ofFn f ↔ ∃ i, f i = a := by
  constructor
  · intro w
    obtain ⟨i, h, rfl⟩ := getElem_of_mem w
    exact ⟨⟨i, by simpa using h⟩, by simp⟩
  · rintro ⟨i, rfl⟩
    apply mem_of_getElem (i := i) <;> simp

end Array
