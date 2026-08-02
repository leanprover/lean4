module

import Init.Data.Array.QSort

/-!
Tests the public correctness theorems for `Array.qsort`.
-/

example (as : Array Nat) (lo hi i : Nat) (hi' : i < as.size)
    (hout : i < lo ∨ hi < i) :
    getElem (as.qsort (· < ·) lo hi) i (by simpa using hi') = as[i] := by
  apply Array.getElem_qsort_of_not_mem <;> assumption
