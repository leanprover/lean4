/-
Copyright (c) 2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
module

prelude
public import Init.Data.Vector.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Vector.Lemmas
import Init.Data.Vector.OfFn
import Init.Omega

public section

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace Vector

/-- `finRange n` is the vector of all elements of `Fin n` in order. -/
protected def finRange (n : Nat) : Vector (Fin n) n := ofFn fun i => i

@[simp, grind =] theorem getElemV_finRange {i : Nat} (h : i < n) :
    (Vector.finRange n)｢i｣ = ⟨i, h⟩ := by
  simp [Vector.finRange, h]

theorem getElem_finRange {i : Nat} (h : i < n) :
    (Vector.finRange n)[i] = ⟨i, h⟩ := by
  simpa using getElemV_finRange h

@[simp] theorem finRange_zero : Vector.finRange 0 = #v[] := by simp [Vector.finRange]

/-
PLOG(finRange_succ):
Had to pull out the side condition into `have`
-/

theorem finRange_succ {n} : Vector.finRange (n+1) =
    (#v[(0 : Fin (n+1))] ++ (Vector.finRange n).map Fin.succ).cast (by omega) := by
  ext i h
  · simp [getElemV_append]
    split
    · simp [*]
    · have : i - 1 < n := by omega
      simp [*]; omega

theorem finRange_succ_last {n} :
    Vector.finRange (n+1) = (Vector.finRange n).map Fin.castSucc ++ #v[Fin.last n] := by
  ext i h
  · simp [getElemV_push, h]
    split
    · simp [*]
    · simp_all
      omega

@[grind _=_]
theorem finRange_reverse {n} : (Vector.finRange n).reverse = (Vector.finRange n).map Fin.rev := by
  ext i h
  have : n - 1 - i < n := by omega
  simp [h, this]
  omega

end Vector
