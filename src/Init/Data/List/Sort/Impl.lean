/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.List.Sort.Lemmas

/-!
# Replacing `merge` and `mergeSort` at runtime with tail-recursive and faster versions.

We replace `merge` with `mergeTR` using a `@[csimp]` lemma.

We replace `mergeSort` in two steps:
* first with `mergeSortTR`, which while not tail-recursive itself (it can't be),
  uses `mergeTR` internally.
* second with `mergeSortTR₂`, which achieves an ~20% speed-up over `mergeSortTR`
  by avoiding some unnecessary list reversals.

There is no public API in this file; it solely exists to implement the `@[csimp]` lemmas
affecting runtime behaviour.

## Future work
The current runtime implementation could be further improved in a number of ways, e.g.:
* only walking the list once during splitting,
* using insertion sort for small chunks rather than splitting all the way down to singletons,
* identifying already sorted or reverse sorted chunks and skipping them.

Because the theory developed for `mergeSort` is independent of the runtime implementation,
as long as such improvements are carefully validated by benchmarking,
they can be done without changing the theory, as long as a `@[csimp]` lemma is provided.
-/

open List

namespace List.MergeSort.Internal

/--
`O(min |l| |r|)`. Merge two lists using `le` as a switch.
-/
def mergeTR (l₁ l₂ : List α) (le : α → α → Bool) : List α :=
  go l₁ l₂ []
where go : List α → List α → List α → List α
  | [], l₂, acc => reverseAux acc l₂
  | l₁, [], acc => reverseAux acc l₁
  | x :: xs, y :: ys, acc =>
    if le x y then
      go xs (y :: ys) (x :: acc)
    else
      go (x :: xs) ys (y :: acc)

theorem mergeTR_go_eq : mergeTR.go le l₁ l₂ acc = acc.reverse ++ merge l₁ l₂ le := by
  induction l₁ generalizing l₂ acc with
  | nil => simp [mergeTR.go, merge, reverseAux_eq]
  | cons x l₁ ih₁ =>
    induction l₂ generalizing acc with
    | nil => simp [mergeTR.go, merge, reverseAux_eq]
    | cons y l₂ ih₂ =>
      simp [mergeTR.go, merge]
      split <;> simp [ih₁, ih₂]

@[csimp] theorem merge_eq_mergeTR : @merge = @mergeTR := by
  funext
  simp [mergeTR, mergeTR_go_eq]

/--
Variant of `splitAt`, that does not reverse the first list, i.e
`splitRevAt n l = ((l.take n).reverse, l.drop n)`.

This exists solely as an optimization for `mergeSortTR` and `mergeSortTR₂`,
and should not be used elsewhere.
-/
def splitRevAt (n : Nat) (l : List α) : List α × List α := go l n [] where
  /-- Auxiliary for `splitAtRev`: `splitAtRev.go xs n acc = ((take n xs).reverse ++ acc, drop n xs)`. -/
  go : List α → Nat → List α → List α × List α
  | x :: xs, n+1, acc => go xs n (x :: acc)
  | xs, _, acc => (acc, xs)

theorem splitRevAt_go (xs : List α) (n : Nat) (acc : List α) :
    splitRevAt.go xs n acc = ((take n xs).reverse ++ acc, drop n xs) := by
  induction xs generalizing n acc with
  | nil => simp [splitRevAt.go]
  | cons x xs ih =>
    cases n with
    | zero => simp [splitRevAt.go]
    | succ n =>
      rw [splitRevAt.go, ih n (x :: acc), take_succ_cons, reverse_cons, drop_succ_cons,
        append_assoc, singleton_append]

theorem splitRevAt_eq (n : Nat) (l : List α) : splitRevAt n l = ((l.take n).reverse, l.drop n) := by
  rw [splitRevAt, splitRevAt_go, append_nil]

/--
An intermediate speed-up for `mergeSort`.
This version uses the tail-recurive `mergeTR` function as a subroutine.

This is not the final version we use at runtime, as `mergeSortTR₂` is faster.
This definition is useful as an intermediate step in proving the `@[csimp]` lemma for `mergeSortTR₂`.
-/
def mergeSortTR (l : List α) (le : α → α → Bool := by exact fun a b => a ≤ b) : List α :=
  run ⟨l, rfl⟩
where run : {n : Nat} → { l : List α // l.length = n } → List α
  | 0, ⟨[], _⟩ => []
  | 1, ⟨[a], _⟩ => [a]
  | _+2, xs =>
    let (l, r) := splitInTwo xs
    mergeTR (run l) (run r) le

/--
Split a list in two equal parts, reversing the first part.
If the length is odd, the first part will be one element longer.
-/
def splitRevInTwo (l : { l : List α // l.length = n }) :
    { l : List α // l.length = (n+1)/2 } × { l : List α // l.length = n/2 } :=
  let r := splitRevAt ((n+1)/2) l.1
  (⟨r.1, by simp [r, splitRevAt_eq, l.2]; omega⟩, ⟨r.2, by simp [r, splitRevAt_eq, l.2]; omega⟩)

/--
Split a list in two equal parts, reversing the first part.
If the length is odd, the second part will be one element longer.
-/
def splitRevInTwo' (l : { l : List α // l.length = n }) :
    { l : List α // l.length = n/2 } × { l : List α // l.length = (n+1)/2 } :=
  let r := splitRevAt (n/2) l.1
  (⟨r.1, by simp [r, splitRevAt_eq, l.2]; omega⟩, ⟨r.2, by simp [r, splitRevAt_eq, l.2]; omega⟩)

/--
Faster version of `mergeSortTR`, which avoids unnecessary list reversals.
-/
-- Per the benchmark in `tests/bench/mergeSort/`
-- (which averages over 4 use cases: already sorted lists, reverse sorted lists, almost sorted lists, and random lists),
-- for lists of length 10^6, `mergeSortTR₂` is about 20% faster than `mergeSortTR`.
def mergeSortTR₂ (l : List α) (le : α → α → Bool := by exact fun a b => a ≤ b) : List α :=
  run ⟨l, rfl⟩
where
  run : {n : Nat} → { l : List α // l.length = n } → List α
  | 0, ⟨[], _⟩ => []
  | 1, ⟨[a], _⟩ => [a]
  | _+2, xs =>
    let (l, r) := splitRevInTwo xs
    mergeTR (run' l) (run r) le
  run' : {n : Nat} → { l : List α // l.length = n } → List α
  | 0, ⟨[], _⟩ => []
  | 1, ⟨[a], _⟩ => [a]
  | _+2, xs =>
    let (l, r) := splitRevInTwo' xs
    mergeTR (run' r) (run l) le

theorem splitRevInTwo'_fst (l : { l : List α // l.length = n }) :
    (splitRevInTwo' l).1 = ⟨(splitInTwo ⟨l.1.reverse, by simpa using l.2⟩).2.1, by simp; omega⟩ := by
  simp only [splitRevInTwo', splitRevAt_eq, reverse_take, splitInTwo_snd]
  congr
  omega
theorem splitRevInTwo'_snd (l : { l : List α // l.length = n }) :
    (splitRevInTwo' l).2 = ⟨(splitInTwo ⟨l.1.reverse, by simpa using l.2⟩).1.1.reverse, by simp; omega⟩ := by
  simp only [splitRevInTwo', splitRevAt_eq, reverse_take, splitInTwo_fst, reverse_reverse]
  congr 2
  simp
  omega
theorem splitRevInTwo_fst (l : { l : List α // l.length = n }) :
    (splitRevInTwo l).1 = ⟨(splitInTwo l).1.1.reverse, by simp; omega⟩ := by
  simp only [splitRevInTwo, splitRevAt_eq, reverse_take, splitInTwo_fst]
theorem splitRevInTwo_snd (l : { l : List α // l.length = n }) :
    (splitRevInTwo l).2 = ⟨(splitInTwo l).2.1, by simp; omega⟩ := by
  simp only [splitRevInTwo, splitRevAt_eq, reverse_take, splitInTwo_snd]

theorem mergeSortTR_run_eq_mergeSort : {n : Nat} → (l : { l : List α // l.length = n }) → mergeSortTR.run le l = mergeSort l.1 le
  | 0, ⟨[], _⟩
  | 1, ⟨[a], _⟩ => by simp [mergeSortTR.run, mergeSort]
  | n+2, ⟨a :: b :: l, h⟩ => by
    cases h
    simp only [mergeSortTR.run, mergeSortTR.run, mergeSort]
    rw [merge_eq_mergeTR]
    rw [mergeSortTR_run_eq_mergeSort, mergeSortTR_run_eq_mergeSort]

-- We don't make this a `@[csimp]` lemma because `mergeSort_eq_mergeSortTR₂` is faster.
theorem mergeSort_eq_mergeSortTR : @mergeSort = @mergeSortTR := by
  funext
  rw [mergeSortTR, mergeSortTR_run_eq_mergeSort]

-- This mutual block is unfortunately quite slow to elaborate.
set_option maxHeartbeats 400000 in
mutual
theorem mergeSortTR₂_run_eq_mergeSort : {n : Nat} → (l : { l : List α // l.length = n }) → mergeSortTR₂.run le l = mergeSort l.1 le
  | 0, ⟨[], _⟩
  | 1, ⟨[a], _⟩ => by simp [mergeSortTR₂.run, mergeSort]
  | n+2, ⟨a :: b :: l, h⟩ => by
    cases h
    simp only [mergeSortTR₂.run, mergeSort]
    rw [splitRevInTwo_fst, splitRevInTwo_snd]
    rw [mergeSortTR₂_run_eq_mergeSort, mergeSortTR₂_run'_eq_mergeSort]
    rw [merge_eq_mergeTR]
    rw [reverse_reverse]
termination_by n => n

theorem mergeSortTR₂_run'_eq_mergeSort : {n : Nat} → (l : { l : List α // l.length = n }) → (w : l' = l.1.reverse) → mergeSortTR₂.run' le l = mergeSort l' le
  | 0, ⟨[], _⟩, w
  | 1, ⟨[a], _⟩, w => by simp_all [mergeSortTR₂.run', mergeSort]
  | n+2, ⟨a :: b :: l, h⟩, w => by
    cases h
    simp only [mergeSortTR₂.run', mergeSort]
    rw [splitRevInTwo'_fst, splitRevInTwo'_snd]
    rw [mergeSortTR₂_run_eq_mergeSort, mergeSortTR₂_run'_eq_mergeSort _ rfl]
    rw [← merge_eq_mergeTR]
    have w' := congrArg length w
    simp at w'
    cases l' with
    | nil => simp at w'
    | cons x l' =>
      cases l' with
      | nil => simp at w'
      | cons y l' =>
        rw [mergeSort]
        congr 2
        · dsimp at w
          simp only [w]
          simp only [splitInTwo_fst, splitInTwo_snd, reverse_take, take_reverse]
          congr 1
          rw [w, length_reverse]
          simp
        · dsimp at w
          simp only [w]
          simp only [reverse_cons, append_assoc, singleton_append, splitInTwo_snd, length_cons]
          congr 1
          simp at w'
          omega
termination_by n => n

end

@[csimp] theorem mergeSort_eq_mergeSortTR₂ : @mergeSort = @mergeSortTR₂ := by
  funext
  rw [mergeSortTR₂, mergeSortTR₂_run_eq_mergeSort]

end List.MergeSort.Internal
