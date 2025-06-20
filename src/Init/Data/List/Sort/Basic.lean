/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
import Init.Data.List.Impl
import Init.Data.List.Nat.TakeDrop

/-!
# Definition of `merge` and `mergeSort`.

These definitions are intended for verification purposes,
and are replaced at runtime by efficient versions in `Init.Data.List.Sort.Impl`.
-/

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace List

/--
Merges two lists, using `le` to select the first element of the resulting list if both are
non-empty.

If both input lists are sorted according to `le`, then the resulting list is also sorted according
to `le`. `O(|xs| + |ys|)`.

This implementation is not tail-recursive, but it is replaced at runtime by a proven-equivalent
tail-recursive merge.
-/
def merge (xs ys : List α) (le : α → α → Bool := by exact fun a b => a ≤ b) : List α :=
  match xs, ys with
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
    if le x y then
      x :: merge xs (y :: ys) le
    else
      y :: merge (x :: xs) ys le

@[simp] theorem nil_merge (ys : List α) : merge [] ys le = ys := by simp [merge]
@[simp] theorem merge_right (xs : List α) : merge xs [] le = xs := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [merge]

/--
Split a list in two equal parts. If the length is odd, the first part will be one element longer.

This is an implementation detail of `mergeSort`.
-/
def MergeSort.Internal.splitInTwo (l : { l : List α // l.length = n }) :
    { l : List α // l.length = (n+1)/2 } × { l : List α // l.length = n/2 } :=
  let r := splitAt ((n+1)/2) l.1
  (⟨r.1, by simp [r, splitAt_eq, l.2]; omega⟩, ⟨r.2, by simp [r, splitAt_eq, l.2]; omega⟩)

open MergeSort.Internal in
set_option linter.unusedVariables false in
/--
A stable merge sort.

This function is a simplified implementation that's designed to be easy to reason about, rather than
for efficiency. In particular, it uses the non-tail-recursive `List.merge` function and traverses
lists unnecessarily.

It is replaced at runtime by an efficient implementation that has been proven to be equivalent.
-/
-- Because we want the sort to be stable, it is essential that we split the list in two contiguous
-- sublists.
def mergeSort : ∀ (xs : List α) (le : α → α → Bool := by exact fun a b => a ≤ b), List α
  | [], _ => []
  | [a], _ => [a]
  | a :: b :: xs, le =>
    let lr := splitInTwo ⟨a :: b :: xs, rfl⟩
    have := by simpa using lr.2.2
    have := by simpa using lr.1.2
    merge (mergeSort lr.1 le) (mergeSort lr.2 le) le
termination_by xs => xs.length

/--
Given an ordering relation `le : α → α → Bool`,
construct the lexicographic ordering on `α × Nat`.
which first compares the first components using `le`,
but if these are equivalent (in the sense `le a.2 b.2 && le b.2 a.2`)
then compares the second components using `≤`.

This function is only used in stating the stability properties of `mergeSort`.
-/
def zipIdxLE (le : α → α → Bool) (a b : α × Nat) : Bool :=
  if le a.1 b.1 then if le b.1 a.1 then a.2 ≤ b.2 else true else false

end List
