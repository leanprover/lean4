/-
Copyright (c) 2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
module

prelude
public import Init.Data.Array.Basic
import Init.Data.Array.Lemmas
import Init.Data.Array.OfFn
import Init.Data.Fin.Lemmas
import Init.Omega

public section

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

@[simp, grind =] theorem size_finRange {n} : (Array.finRange n).size = n := by
  simp [Array.finRange]

@[simp, grind =] theorem getElemV_finRange {i : Nat} (h : i < n) :
    haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    (Array.finRange n)｢i｣ = Fin.cast size_finRange ⟨i, by simpa using h⟩ := by
  simp [Array.finRange, getElemV_ofFn h]

@[simp, grind =] theorem getElem_finRange {i : Nat} (h : i < (Array.finRange n).size) :
    (Array.finRange n)[i] = Fin.cast size_finRange ⟨i, h⟩ := by
  simpa using getElemV_finRange (by simpa using h)

@[simp] theorem finRange_zero : Array.finRange 0 = #[] := by simp [Array.finRange]

/-
PLOG(finRange_succ):
Again, the `rw` + side condition proofs pattern seemed most robust even though it's verbose.
-/

theorem finRange_succ {n} : Array.finRange (n+1) = #[0] ++ (Array.finRange n).map Fin.succ := by
  ext i h₁ h₂
  · simp [Nat.add_comm]
  · simp [getElemV_append]
    split
    · rw [getElemV_finRange] <;> simp [*]
    · rw [getElemV_finRange, getElemV_map, getElemV_finRange]
      · simp only [Fin.cast_mk, Fin.succ_mk]; omega
      · have : 1 ≤ i := by omega
        simpa [Nat.sub_lt_iff_lt_add, *] using h₁
      · have : 1 ≤ i := by omega
        simpa [Nat.sub_lt_iff_lt_add, *] using h₁
      · simpa using h₁

/-
PLOG(finRange_succ_last):
Another case where the side conditions are annoying
-/

theorem finRange_succ_last {n} :
    Array.finRange (n+1) = (Array.finRange n).map Fin.castSucc ++ #[Fin.last n] := by
  apply ext_getElemV
  · simp
  · intro i hi
    ext
    rw [append_singleton, getElemV_push]; rotate_left
    · simpa [Nat.lt_add_one_iff] using hi
    split
    · rename_i hi'
      rw [getElemV_finRange, getElemV_map, getElemV_finRange]
      · simp
      · simpa using hi'
      · simpa using hi'
      · simpa using hi
    · rw [getElemV_finRange]
      · simp_all
        omega
      · simpa using hi

/-
PLOG(finRange_reverse):
requires manual bounds proofs, too
-/

@[grind _=_]
theorem finRange_reverse {n} : (Array.finRange n).reverse = (Array.finRange n).map Fin.rev := by
  apply ext_getElemV
  · simp
  · intro i hi
    ext
    rw [getElemV_reverse, getElemV_finRange, getElemV_map, getElemV_finRange]
    · simp; omega
    · simpa using hi
    · simpa using hi
    · simp at hi ⊢; omega
    · simp at hi ⊢; omega

end Array
