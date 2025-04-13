/-
Copyright (c) 2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
prelude
import Init.Data.List.FinRange
import Init.Data.Array.OfFn

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace Array

/--
Returns an array of all elements of `Fin n` in order, starting at `0`.

Examples:
 * `Array.finRange 0 = (#[] : Array (Fin 0))`
 * `Array.finRange 2 = (#[0, 1] : Array (Fin 2))`
-/
protected def finRange (n : Nat) : Array (Fin n) := ofFn fun i => i

@[simp] theorem size_finRange {n} : (Array.finRange n).size = n := by
  simp [Array.finRange]

@[simp] theorem getElem_finRange {i : Nat} (h : i < (Array.finRange n).size) :
    (Array.finRange n)[i] = Fin.cast size_finRange ⟨i, h⟩ := by
  simp [Array.finRange]

@[simp] theorem finRange_zero : Array.finRange 0 = #[] := by simp [Array.finRange]

theorem finRange_succ {n} : Array.finRange (n+1) = #[0] ++ (Array.finRange n).map Fin.succ := by
  ext
  · simp [Nat.add_comm]
  · simp [getElem_append]
    split <;>
    · simp; omega

theorem finRange_succ_last {n} :
    Array.finRange (n+1) = (Array.finRange n).map Fin.castSucc ++ #[Fin.last n] := by
  ext
  · simp
  · simp [getElem_push]
    split
    · simp
    · simp_all
      omega

theorem finRange_reverse {n} : (Array.finRange n).reverse = (Array.finRange n).map Fin.rev := by
  ext i h
  · simp
  · simp
    omega

end Array
