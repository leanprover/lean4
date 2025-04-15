/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.Vector.Lemmas
import Init.Data.Array.OfFn

/-!
# Theorems about `Vector.ofFn`
-/

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace Vector

@[simp] theorem getElem_ofFn {α n} {f : Fin n → α} (h : i < n) :
    (Vector.ofFn f)[i] = f ⟨i, by simpa using h⟩ := by
  simp [ofFn]

theorem getElem?_ofFn {α n} {f : Fin n → α} :
    (ofFn f)[i]? = if h : i < n then some (f ⟨i, h⟩) else none := by
  simp [getElem?_def]

@[simp 500]
theorem mem_ofFn {n} {f : Fin n → α} {a : α} : a ∈ ofFn f ↔ ∃ i, f i = a := by
  constructor
  · intro w
    obtain ⟨i, h, rfl⟩ := getElem_of_mem w
    exact ⟨⟨i, by simpa using h⟩, by simp⟩
  · rintro ⟨i, rfl⟩
    apply mem_of_getElem (i := i) <;> simp

theorem back_ofFn {n} [NeZero n] {f : Fin n → α} :
    (ofFn f).back = f ⟨n - 1, by have := NeZero.ne n; omega⟩ := by
  simp [back]

end Vector
