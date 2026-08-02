/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Init.Data.Vector.Basic
public import Init.Data.Ord.Basic
import Init.Omega

public section

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
-- We do not enable `linter.indexVariables` because it is helpful to name index variables `lo`, `mid`, `hi`, etc.


namespace Array

/--
Internal implementation of `Array.qsort`.

`qpartition as cmp lo hi hlo hhi` returns a pair `(⟨(m₁, m₂), h⟩, as')` where
`as'` is a permutation of `as` and `lo ≤ m₁ < m₂ ≤ hi + 1`. The active range is
partitioned into elements smaller than, equal to, and greater than the pivot at the boundaries
`m₁` and `m₂`.

It does so by first swapping the elements at indices `lo`, `mid := (lo + hi) / 2`, and `hi`
if necessary so that the middle (pivot) element is at index `hi`.
The pivot is kept at `hi` while the rest of the range is partitioned. This guarantees that the
middle range is nonempty even when `cmp` is not a lawful comparison function.
-/
@[inline]
def qpartition {n} (as : Vector α n) (cmp : α → α → Ordering) (lo hi : Nat)
    (w : lo ≤ hi := by omega) (hlo : lo < n := by omega) (hhi : hi < n := by omega) :
    {m : Nat × Nat // lo ≤ m.1 ∧ m.1 < m.2 ∧ m.2 ≤ hi + 1} × Vector α n :=
  let mid := (lo + hi) / 2
  let as  := if (cmp as[mid] as[lo]).isLT then as.swap lo mid else as
  let as  := if (cmp as[hi]  as[lo]).isLT then as.swap lo hi  else as
  let as  := if (cmp as[mid] as[hi]).isLT then as.swap mid hi else as
  let pivot := as[hi]
  -- Once an element equal to the pivot has been found, `[lo, i)` is smaller,
  -- `[i, k)` is equal, `[k, j)` is unexamined, and `[j, hi)` is greater.
  let rec @[specialize] eqLoop (as : Vector α n) (i k j : Nat)
      (ilo : lo ≤ i := by omega) (ik : i ≤ k := by omega) (kj : k ≤ j := by omega)
      (jhi : j ≤ hi := by omega) :=
    if h : k < j then
      match cmp as[k] pivot with
      | .lt => eqLoop (as.swap i k) (i + 1) (k + 1) j
      | .eq => eqLoop as i (k + 1) j
      | .gt =>
        if h' : k + 1 < j then
          match cmp as[j - 1] pivot with
          | .lt => eqLoop ((as.swap k (j - 1)).swap i k) (i + 1) (k + 1) (j - 1)
          | .eq => eqLoop (as.swap k (j - 1)) i (k + 1) (j - 1)
          | .gt => eqLoop as i k (j - 1)
        else
          eqLoop as i k (j - 1)
    else
      (⟨(i, j + 1), ilo, by omega⟩, as.swap j hi)
  -- Before seeing an equal element, collect only smaller elements. This keeps the hot path for
  -- distinct data small; on finding equality, the greater prefix becomes unexamined again.
  let rec @[specialize] loop (as : Vector α n) (i k : Nat)
      (ilo : lo ≤ i := by omega) (ik : i ≤ k := by omega) (khi : k ≤ hi := by omega) :=
    if h : k < hi then
      match cmp as[k] pivot with
      | .lt => loop (as.swap i k) (i + 1) (k + 1)
      | .gt => loop as i (k + 1)
      | .eq => eqLoop (as.swap i k) i (i + 1) hi
    else
      (⟨(i, i + 1), ilo, by omega⟩, as.swap i hi)
  loop as lo lo

@[inline]
private def compareOfLess (lt : α → α → Bool) (a b : α) : Ordering :=
  if lt a b then .lt else if lt b a then .gt else .eq

@[inline]
private def qsortBy (as : Array α) (cmp : α → α → Ordering) (lo hi : Nat) : Array α :=
  let rec @[specialize] sort {n} (as : Vector α n) (lo hi : Nat) (w : lo ≤ hi := by omega)
      (hhi : hi ≤ n := by omega) :=
    if h : lo + 1 < hi then
      let ⟨⟨(mid₁, mid₂), hmids⟩, as⟩ := qpartition as cmp lo (hi - 1)
      sort (sort as lo mid₁) mid₂ hi
    else as
  termination_by hi - lo
  if h : as.size = 0 then
    as
  else
    let lo := min lo (as.size - 1)
    let hi := max lo (min hi (as.size - 1))
    sort as.toVector lo (hi + 1) |>.toArray

/--
In-place quicksort.

`qsort as lt lo hi` sorts the subarray `as[lo...=hi]` in-place using `lt` to compare elements.
-/
@[inline] def qsort (as : Array α) (lt : α → α → Bool := by exact (· < ·))
    (lo := 0) (hi := as.size - 1) : Array α :=
  qsortBy as (compareOfLess lt) lo hi

set_option linter.unusedVariables.funArgs false in
/--
Sort an array using `compare` to compare elements.
-/
def qsortOrd [ord : Ord α] (xs : Array α) : Array α :=
  qsortBy xs compare 0 (xs.size - 1)

end Array
