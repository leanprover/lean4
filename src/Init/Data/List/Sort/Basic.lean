/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.List.Impl

/-!
# Definition of `merge` and `mergeSort`.

These definitions are intended for verification purposes,
and are replaced at runtime by efficient versions in `Init.Data.List.Sort.Impl`.
-/

namespace List

/--
`O(min |l| |r|)`. Merge two lists using `le` as a switch.

This version is not tail-recursive,
but it is replaced at runtime by `mergeTR` using a `@[csimp]` lemma.
-/
def merge (le : α → α → Bool) : List α → List α → List α
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
    if le x y then
      x :: merge le xs (y :: ys)
    else
      y :: merge le (x :: xs) ys

@[simp] theorem nil_merge (ys : List α) : merge le [] ys = ys := by simp [merge]
@[simp] theorem merge_right (xs : List α) : merge le xs [] = xs := by
  induction xs with
  | nil => simp [merge]
  | cons x xs ih => simp [merge, ih]

/--
Split a list in two equal parts. If the length is odd, the first part will be one element longer.
-/
def splitInTwo (l : { l : List α // l.length = n }) :
    { l : List α // l.length = (n+1)/2 } × { l : List α // l.length = n/2 } :=
  let r := splitAt ((n+1)/2) l.1
  (⟨r.1, by simp [r, splitAt_eq, l.2]; omega⟩, ⟨r.2, by simp [r, splitAt_eq, l.2]; omega⟩)

/--
Simplified implementation of stable merge sort.

This function is designed for reasoning about the algorithm, and is not efficient.
(It particular it uses the non tail-recursive `merge` function,
and so can not be run on large lists, but also makes unnecessary traversals of lists.)
It is replaced at runtime in the compiler by `mergeSortTR₂` using a `@[csimp]` lemma.

Because we want the sort to be stable,
it is essential that we split the list in two contiguous sublists.
-/
def mergeSort (le : α → α → Bool) : List α → List α
  | [] => []
  | [a] => [a]
  | a :: b :: xs =>
    let lr := splitInTwo ⟨a :: b :: xs, rfl⟩
    have := by simpa using lr.2.2
    have := by simpa using lr.1.2
    merge le (mergeSort le lr.1) (mergeSort le lr.2)
termination_by l => l.length


/--
Given an ordering relation `le : α → α → Bool`,
construct the reverse lexicographic ordering on `Nat × α`.
which first compares the second components using `le`,
but if these are equivalent (in the sense `le a.2 b.2 && le b.2 a.2`)
then compares the first components using `≤`.

This function is only used in stating the stability properties of `mergeSort`.
-/
def enumLE (le : α → α → Bool) (a b : Nat × α) : Bool :=
  if le a.2 b.2 then if le b.2 a.2 then a.1 ≤ b.1 else true else false

end List
