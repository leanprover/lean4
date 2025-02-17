/-
Copyright (c) 2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
prelude
import Init.Data.Array.FinRange
import Init.Data.Vector.OfFn

namespace Vector

/-- `finRange n` is the vector of all elements of `Fin n` in order. -/
protected def finRange (n : Nat) : Vector (Fin n) n := ofFn fun i => i

@[simp] theorem getElem_finRange (i : Nat) (h : i < n) :
    (Vector.finRange n)[i] = ⟨i, h⟩ := by
  simp [Vector.finRange]

@[simp] theorem finRange_zero : Vector.finRange 0 = #v[] := by simp [Vector.finRange]

theorem finRange_succ (n) : Vector.finRange (n+1) =
    (#v[(0 : Fin (n+1))] ++ (Vector.finRange n).map Fin.succ).cast (by omega) := by
  ext i h
  · simp [getElem_append]
    split <;>
    · simp; omega

theorem finRange_succ_last (n) :
    Vector.finRange (n+1) = (Vector.finRange n).map Fin.castSucc ++ #v[Fin.last n] := by
  ext i h
  · simp [getElem_push]
    split
    · simp
    · simp_all
      omega

theorem finRange_reverse (n) : (Vector.finRange n).reverse = (Vector.finRange n).map Fin.rev := by
  ext i h
  simp
  omega

end Vector
