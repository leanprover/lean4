/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Vector.Basic
import Init.Data.Ord

namespace Array

private def qpartition {n} (as : Vector α n) (lt : α → α → Bool) (lo hi : Nat)
    (hlo : lo < n := by omega) (hhi : hi < n := by omega) : {n : Nat // lo ≤ n} × Vector α n :=
  let mid := (lo + hi) / 2
  let as  := if lt as[mid] as[lo] then as.swap lo mid else as
  let as  := if lt as[hi]  as[lo] then as.swap lo hi  else as
  let as  := if lt as[mid] as[hi] then as.swap mid hi else as
  let pivot := as[hi]
  let rec loop (as : Vector α n) (i j : Nat)
      (ilo : lo ≤ i := by omega) (jh : j < n := by omega) (w : i ≤ j := by omega) :=
    if h : j < hi then
      if lt as[j] pivot then
        loop (as.swap i j) (i+1) (j+1)
      else
        loop as i (j+1)
    else
      (⟨i, ilo⟩, as.swap i hi)
  loop as lo lo

@[inline] def qsort (as : Array α) (lt : α → α → Bool := by exact (· < ·))
    (low := 0) (high := as.size - 1) : Array α :=
  let rec @[specialize] sort {n} (as : Vector α n) (lo hi : Nat)
      (hlo : lo < n := by omega) (hhi : hi < n := by omega) :=
    if h₁ : lo < hi then
      let ⟨⟨mid, hmid⟩, as⟩ := qpartition as lt lo hi
      if h₂ : mid ≥ hi then
        as
      else
        sort (sort as lo mid) (mid+1) hi
    else as
  if h : as.size = 0 then
    as
  else
    let low := min low (as.size - 1)
    let high := min high (as.size - 1)
    sort ⟨as, rfl⟩ low high |>.toArray

set_option linter.unusedVariables.funArgs false in
/--
Sort an array using `compare` to compare elements.
-/
def qsortOrd [ord : Ord α] (xs : Array α) : Array α :=
  xs.qsort fun x y => compare x y |>.isLT

end Array
