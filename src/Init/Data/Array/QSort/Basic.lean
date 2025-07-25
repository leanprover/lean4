/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Init.Data.Vector.Basic
public import Init.Data.Ord

public section

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
-- We do not enable `linter.indexVariables` because it is helpful to name index variables `lo`, `mid`, `hi`, etc.


namespace Array

/--
Internal implementation of `Array.qsort`.

`qpartition as lt lo hi hlo hhi` returns a pair `(⟨m, h₁, h₂⟩, as')` where
`as'` is a permutation of `as` and `m` is a number such that:
- `lo ≤ m`
- `m < n`
- `∀ i, lo ≤ i → i < m → lt as[i] as[m]`
- `∀ j, m < j → j < hi → !lt as[j] as[m]`

It does so by first swapping the elements at indices `lo`, `mid := (lo + hi) / 2`, and `hi`
if necessary so that the middle (pivot) element is at index `hi`.
We then iterate from `k = lo` to `k = hi`, with a pointer `i` starting at `lo`, and
swapping each element which is less than the pivot to position `i`, and then incrementing `i`.
-/
def qpartition {n} (as : Vector α n) (cmp : α → α → Ordering) (lo hi : Nat) (w : lo ≤ hi := by omega)
    (hlo : lo < n := by omega) (hhi : hi < n := by omega) : { p : Nat × Nat // lo ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ hi } × Vector α n :=
  let pivot := as[(lo + hi) / 2]
  -- During this loop, elements in `[lo, i)` are less than `pivot`,
  -- elements in `[i, j)` are equal to `pivot`,
  -- elements in `[j, k]` are unexamined,
  -- elements in `(k, hi]` are greater than `pivot`,
  let rec loop (as : Vector α n) (i j k : Nat)
      (ilo : lo ≤ i := by omega) (ij : i ≤ j := by omega) (jk : j ≤ k := by omega) (w : k ≤ hi := by omega) :=
    if h : j < k then
      match cmp as[j] pivot with
      | .lt => loop (as.swap i j) (i+1) (j+1) k
      | .gt => loop (as.swap j k) i j (k-1)
      | .eq => loop as i (j+1) k
    else
      match cmp as[j] pivot with
      | .lt => ⟨⟨⟨i+1, k+1⟩, by sorry⟩, as.swap i j⟩
      | .gt => ⟨⟨⟨i, k⟩, by omega⟩, as.swap j k⟩
      | .eq => ⟨⟨⟨i, k+1⟩, by sorry⟩, as⟩
  loop as lo lo hi

/--
In-place quicksort.

`qsort as lt lo hi` sorts the subarray `as[lo...=hi]` in-place using `cmp` to compare elements.
-/
@[inline] def qsort (as : Array α) (cmp : α → α → Ordering := by exact (compareOfLessAndEq · ·))
    (lo := 0) (hi := as.size - 1) : Array α :=
  let rec @[specialize] sort {n} (as : Vector α n) (lo hi : Nat) (w : lo ≤ hi := by omega)
      (hlo : lo < n := by omega) (hhi : hi < n := by omega) :=
    if h₁ : lo < hi then
      let ⟨⟨⟨i, k⟩, h₁, h₂, h₃⟩, as⟩ := qpartition as cmp lo hi
      sort (sort as lo (i-1)) k hi
    else as
  if h : as.size = 0 then
    as
  else
    let lo := min lo (as.size - 1)
    let hi := max lo (min hi (as.size - 1))
    sort as.toVector lo hi |>.toArray

set_option linter.unusedVariables.funArgs false in
/--
Sort an array using `compare` to compare elements.
-/
def qsortOrd [ord : Ord α] (xs : Array α) : Array α :=
  xs.qsort compare

end Array
