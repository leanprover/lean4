/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude

import Init.Data.List.Nat.Sublist
import Init.Data.List.Nat.Pairwise
import Init.Data.List.Nat.Range
import Init.Data.List.Perm
import Init.Data.List.Impl
-- import Lean.Eval

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

abbrev Sorted (le : α → α → Prop) (xs : List α) : Prop := xs.Pairwise le

-- instance boolPredToPred : Coe (α → Bool) (α  → Prop) where
--   coe r := fun a => r a = true
-- instance boolRelToRel : Coe (α → α → Bool) (α → α → Prop) where
--   coe r := fun a b => r a b = true

@[simp] theorem splitInTwo_fst (l : { l : List α // l.length = n }) : (splitInTwo l).1 = ⟨l.1.take ((n+1)/2), by simp [splitInTwo, splitAt_eq, l.2]; omega⟩ := by
  simp [splitInTwo, splitAt_eq]

@[simp] theorem splitInTwo_snd (l : { l : List α // l.length = n }) : (splitInTwo l).2 = ⟨l.1.drop ((n+1)/2), by simp [splitInTwo, splitAt_eq, l.2]; omega⟩ := by
  simp [splitInTwo, splitAt_eq]

theorem splitInTwo_fst_append_splitInTwo_snd (l : { l : List α // l.length = n }) : (splitInTwo l).1.1 ++ (splitInTwo l).2.1 = l.1 := by
  simp

variable {le : α → α → Bool}

@[simp] theorem merge_nil_right (xs : List α) : merge le xs [] = xs := by
  induction xs with
  | nil => simp [merge]
  | cons x xs ih => simp [merge, ih]



theorem mem_merge {a : α} {xs ys : List α} : a ∈ merge le xs ys ↔ a ∈ xs ∨ a ∈ ys := by
  induction xs generalizing ys with
  | nil => simp [merge]
  | cons x xs ih =>
    induction ys with
    | nil => simp [merge]
    | cons y ys ih =>
      simp only [merge]
      split <;> rename_i h
      · simp_all [or_assoc]
      · simp only [mem_cons, or_assoc, Bool.not_eq_true, ih, ← or_assoc]
        apply or_congr_left
        simp only [or_comm (a := a = y), or_assoc]

theorem merge_sorted
    (trans : ∀ (a b c : α), le a b → le b c → le a c)
    (total : ∀ (a b : α), !le a b → le b a)
    (l₁ l₂ : List α) (h₁ : l₁.Sorted le) (h₂ : l₂.Sorted le) : (merge le l₁ l₂).Sorted le := by
  induction l₁ generalizing l₂ with
  | nil => simpa only [merge]
  | cons x l₁ ih₁ =>
    induction l₂ with
    | nil => simpa only [merge]
    | cons y l₂ ih₂ =>
      simp only [merge]
      split <;> rename_i h
      · apply Pairwise.cons
        · intro z m
          rw [mem_merge, mem_cons] at m
          rcases m with (m|rfl|m)
          · exact rel_of_pairwise_cons h₁ m
          · exact h
          · exact trans _ _ _ h (rel_of_pairwise_cons h₂ m)
        · exact ih₁ _ h₁.tail h₂
      · apply Pairwise.cons
        · intro z m
          rw [mem_merge, mem_cons] at m
          rcases m with (⟨rfl|m⟩|m)
          · exact total _ _ (by simpa using h)
          · exact trans _ _ _ (total _ _ (by simpa using h)) (rel_of_pairwise_cons h₁ m)
          · exact rel_of_pairwise_cons h₂ m
        · exact ih₂ h₂.tail

theorem splitInTwo_fst_sorted (l : { l : List α // l.length = n }) (h : Sorted le l.1) : Sorted le (splitInTwo l).1.1 := by
  rw [splitInTwo_fst]
  exact h.take

theorem splitInTwo_snd_sorted (l : { l : List α // l.length = n }) (h : Sorted le l.1) : Sorted le (splitInTwo l).2.1 := by
  rw [splitInTwo_snd]
  exact h.drop

theorem splitInTwo_fst_le_splitInTwo_snd {l : { l : List α // l.length = n }} (h : Sorted le l.1) :
    ∀ a b, a ∈ (splitInTwo l).1.1 → b ∈ (splitInTwo l).2.1 → le a b := by
  rw [splitInTwo_fst, splitInTwo_snd]
  intro a b ma mb
  exact h.rel_of_mem_take_of_mem_drop ma mb

theorem merge_of_le : ∀ {xs ys : List α} (_ : ∀ a b, a ∈ xs → b ∈ ys → le a b),
    merge le xs ys = xs ++ ys
  | [], ys, _
  | xs, [], _ => by simp [merge]
  | x :: xs, y :: ys, h => by
    simp only [merge, cons_append]
    rw [if_pos, merge_of_le]
    · intro a b ma mb
      exact h a b (mem_cons_of_mem _ ma) mb
    · exact h x y (mem_cons_self _ _) (mem_cons_self _ _)

def stable_le (le : α → α → Bool) (a b : Nat × α) : Bool :=
  if le a.2 b.2 then if le b.2 a.2 then a.1 ≤ b.1 else true else false

theorem stable_le_trans (trans : ∀ a b c, le a b → le b c → le a c)
    (a b c : Nat × α) : stable_le le a b → stable_le le b c → stable_le le a c := by
  simp only [stable_le]
  split <;> split <;> split <;> rename_i ab₂ ba₂ bc₂
  · simp_all
    intro ab₁
    intro h
    refine ⟨trans _ _ _ ab₂ bc₂, ?_⟩
    rcases h with (cd₂ | bc₁)
    · exact Or.inl (Decidable.byContradiction
        (fun ca₂ => by simp_all [trans _ _ _ (by simpa using ca₂) ab₂]))
    · exact Or.inr (Nat.le_trans ab₁ bc₁)
  · simp_all
  · simp_all
    intro h
    refine ⟨trans _ _ _ ab₂ bc₂, ?_⟩
    left
    rcases h with (cb₂ | _)
    · exact (Decidable.byContradiction
        (fun ca₂ => by simp_all [trans _ _ _ (by simpa using ca₂) ab₂]))
    · exact (Decidable.byContradiction
        (fun ca₂ => by simp_all [trans _ _ _ bc₂ (by simpa using ca₂)]))
  · simp_all
  · simp_all
  · simp_all
  · simp_all
  · simp_all

theorem stable_le_total (total : ∀ a b, !le a b → le b a)
    (a b : Nat × α) : !stable_le le a b → stable_le le b a := by
  simp only [stable_le]
  split <;> split
  · simpa using Nat.le_of_lt
  · simp
  · simp
  · simp_all [total a.2 b.2]

theorem splitInTwo_cons_cons_enumFrom_fst (i : Nat) (l : List α) :
    (splitInTwo ⟨(i, a) :: (i+1, b) :: l.enumFrom (i+2), rfl⟩).1.1 =
      (splitInTwo ⟨a :: b :: l, rfl⟩).1.1.enumFrom i := by
  simp only [length_cons, splitInTwo_fst, enumFrom_length]
  ext1 j
  rw [getElem?_take, getElem?_enumFrom, getElem?_take]
  split
  · rw [getElem?_cons, getElem?_cons, getElem?_cons, getElem?_cons]
    split
    · simp; omega
    · split
      · simp; omega
      · simp only [getElem?_enumFrom]
        congr
        ext <;> simp; omega
  · simp

theorem splitInTwo_cons_cons_enumFrom_snd (i : Nat) (l : List α) :
    (splitInTwo ⟨(i, a) :: (i+1, b) :: l.enumFrom (i+2), rfl⟩).2.1 =
      (splitInTwo ⟨a :: b :: l, rfl⟩).2.1.enumFrom (i+(l.length+3)/2) := by
  simp only [length_cons, splitInTwo_snd, enumFrom_length]
  ext1 j
  rw [getElem?_drop, getElem?_enumFrom, getElem?_drop]
  rw [getElem?_cons, getElem?_cons, getElem?_cons, getElem?_cons]
  split
  · simp; omega
  · split
    · simp; omega
    · simp only [getElem?_enumFrom]
      congr
      ext <;> simp; omega

theorem merge_stable : ∀ (xs ys) (_ : ∀ x y, x ∈ xs → y ∈ ys → x.1 ≤ y.1),
    (merge (stable_le le) xs ys).map (·.2) = merge le (xs.map (·.2)) (ys.map (·.2))
  | [], ys, _ => by simp [merge]
  | xs, [], _ => by simp [merge]
  | (i, x) :: xs, (j, y) :: ys, h => by
    simp only [merge, stable_le, map_cons]
    split <;> rename_i w
    · rw [if_pos (by simp [h _ _ (mem_cons_self ..) (mem_cons_self ..)])]
      simp only [map_cons, cons.injEq, true_and]
      rw [merge_stable, map_cons]
      exact fun x' y' mx my => h x' y' (mem_cons_of_mem (i, x) mx) my
    · simp only [↓reduceIte, map_cons, cons.injEq, true_and]
      rw [merge_stable, map_cons]
      exact fun x' y' mx my => h x' y' mx (mem_cons_of_mem (j, y) my)

theorem merge_perm_append : ∀ {xs ys : List α}, merge le xs ys ~ xs ++ ys
  | [], ys => by simp [merge]
  | xs, [] => by simp [merge]
  | x :: xs, y :: ys => by
    simp only [merge]
    split
    · exact merge_perm_append.cons x
    · exact (merge_perm_append.cons y).trans
        ((Perm.swap x y _).trans (perm_middle.symm.cons x))

variable (le) in
theorem mergeSort_perm : ∀ (l : List α), mergeSort le l ~ l
  | [] => by simp [mergeSort]
  | [a] => by simp [mergeSort]
  | a :: b :: xs => by
    simp only [mergeSort]
    have : (splitInTwo ⟨a :: b :: xs, rfl⟩).1.1.length < xs.length + 1 + 1 := by simp [splitInTwo_fst]; omega
    have : (splitInTwo ⟨a :: b :: xs, rfl⟩).2.1.length < xs.length + 1 + 1 := by simp [splitInTwo_snd]; omega
    exact merge_perm_append.trans
      (((mergeSort_perm _).append (mergeSort_perm _)).trans
        (Perm.of_eq (splitInTwo_fst_append_splitInTwo_snd _)))
termination_by l => l.length

@[simp] theorem mem_mergeSort {a : α} {l : List α} : a ∈ mergeSort le l ↔ a ∈ l :=
  (mergeSort_perm le l).mem_iff

/--
The result of `mergeSort` is sorted,
as long as the comparison function is transitive (`le a b → le b c → le a c`)
and total in the sense that `le a b ∨ le b a`.

The comparison function need not be irreflexive, i.e. `le a b` and `le b a` is allowed even when `a ≠ b`.
-/
theorem mergeSort_sorted
    (trans : ∀ (a b c : α), le a b → le b c → le a c)
    (total : ∀ (a b : α), !le a b → le b a) :
    (l : List α) → (mergeSort le l).Sorted le
  | [] => by simp [mergeSort]
  | [a] => by simp [mergeSort]
  | a :: b :: xs => by
    have : (splitInTwo ⟨a :: b :: xs, rfl⟩).1.1.length < xs.length + 1 + 1 := by simp [splitInTwo_fst]; omega
    have : (splitInTwo ⟨a :: b :: xs, rfl⟩).2.1.length < xs.length + 1 + 1 := by simp [splitInTwo_snd]; omega
    rw [mergeSort]
    apply merge_sorted @trans @total
    apply mergeSort_sorted trans total
    apply mergeSort_sorted trans total
termination_by l => l.length

/--
If the input list is already sorted, then `mergeSort` does not change the list.
-/
theorem mergeSort_of_sorted : ∀ {l : List α} (_ : Sorted le l), mergeSort le l = l
  | [], _ => by simp [mergeSort]
  | [a], _ => by simp [mergeSort]
  | a :: b :: xs, h => by
    have : (splitInTwo ⟨a :: b :: xs, rfl⟩).1.1.length < xs.length + 1 + 1 := by simp [splitInTwo_fst]; omega
    have : (splitInTwo ⟨a :: b :: xs, rfl⟩).2.1.length < xs.length + 1 + 1 := by simp [splitInTwo_snd]; omega
    rw [mergeSort]
    rw [mergeSort_of_sorted (splitInTwo_fst_sorted ⟨a :: b :: xs, rfl⟩ h)]
    rw [mergeSort_of_sorted (splitInTwo_snd_sorted ⟨a :: b :: xs, rfl⟩ h)]
    rw [merge_of_le (splitInTwo_fst_le_splitInTwo_snd h)]
    rw [splitInTwo_fst_append_splitInTwo_snd]
termination_by l => l.length

/--
This merge sort algorithm is stable,
in the sense that breaking ties in the ordering function using the position in the list
has no effect on the output.

That is, elements which are equal with respect to the ordering function will remain
in the same order in the output list as they were in the input list.

See also:
* `mergeSort_stable`: if `c <+ l` and `c.Pairwise le`, then `c <+ mergeSort le l`.
* `mergeSort_stable_pair`: if `[a, b] <+ l` and `le a b`, then `[a, b] <+ mergeSort le l`)
-/
theorem mergeSort_enum {l : List α} :
    (mergeSort (stable_le le) (l.enum)).map (·.2) = mergeSort le l :=
  go 0 l
where go : ∀ (i : Nat) (l : List α),
    (mergeSort (stable_le le) (l.enumFrom i)).map (·.2) = mergeSort le l
  | _, []
  | _, [a] => by simp [mergeSort]
  | _, a :: b :: xs => by
    have : (splitInTwo ⟨a :: b :: xs, rfl⟩).1.1.length < xs.length + 1 + 1 := by simp [splitInTwo_fst]; omega
    have : (splitInTwo ⟨a :: b :: xs, rfl⟩).2.1.length < xs.length + 1 + 1 := by simp [splitInTwo_snd]; omega
    simp only [mergeSort, enumFrom]
    rw [splitInTwo_cons_cons_enumFrom_fst]
    rw [splitInTwo_cons_cons_enumFrom_snd]
    rw [merge_stable]
    · rw [go, go]
    · simp only [mem_mergeSort, Prod.forall]
      intros j x k y mx my
      have := mem_enumFrom mx
      have := mem_enumFrom my
      simp_all
      omega
termination_by _ l => l.length

theorem eq_middle_of_mem {l : List α} : a ∈ l → ∃ l₁ l₂, l = l₁ ++ a :: l₂
  | .head l => ⟨[], l, by simp⟩
  | .tail a h => by
    obtain ⟨l₁, l₂, rfl⟩ := eq_middle_of_mem h
    exact ⟨a :: l₁, l₂, by simp⟩

theorem Perm.eq_of_sorted : ∀ {l₁ l₂ : List α}
    (_ : ∀ a b, a ∈ l₁ → b ∈ l₂ → le a b → le b a → a = b)
    (_ : l₁.Sorted le) (_ : l₂.Sorted le) (_ : l₁ ~ l₂), l₁ = l₂
  | [], [], _, _, _, _ => rfl
  | [], b :: l₂, _, _, _, h => by simp_all
  | a :: l₁, [], _, _, _, h => by simp_all
  | a :: l₁, b :: l₂, w, h₁, h₂, h => by
    have am : a ∈ b :: l₂ := h.subset (mem_cons_self _ _)
    have bm : b ∈ a :: l₁ := h.symm.subset (mem_cons_self _ _)
    have ab : a = b := by
      simp only [mem_cons] at am
      rcases am with rfl | am
      · rfl
      · simp only [mem_cons] at bm
        rcases bm with rfl | bm
        · rfl
        · exact w _ _ (mem_cons_self _ _) (mem_cons_self _ _)
            (rel_of_pairwise_cons h₁ bm) (rel_of_pairwise_cons h₂ am)
    subst ab
    simp only [perm_cons] at h
    have := Perm.eq_of_sorted ?_ h₁.tail h₂.tail h
    simp_all
    intro a b ha hb
    exact w a b (mem_cons_of_mem _ ha) (mem_cons_of_mem _ hb)

theorem mergeSort_cons {le : α → α → Bool}
    (trans : ∀ (a b c : α), le a b → le b c → le a c)
    (total : ∀ (a b : α), !le a b → le b a)
    (a : α) (l : List α) :
    ∃ l₁ l₂, mergeSort le (a :: l) = l₁ ++ a :: l₂ ∧ mergeSort le l = l₁ ++ l₂ ∧
      ∀ b, b ∈ l₁ → !le a b := by
  rw [← mergeSort_enum]
  rw [enum_cons]
  have nd : Nodup ((a :: l).enum.map (·.1)) := by rw [enum_map_fst]; exact nodup_range _
  have m₁ : (0, a) ∈ mergeSort (stable_le le) ((a :: l).enum) :=
    mem_mergeSort.mpr (mem_cons_self _ _)
  obtain ⟨l₁, l₂, h⟩ := eq_middle_of_mem m₁
  have s := mergeSort_sorted (stable_le_trans trans) (stable_le_total total) ((a :: l).enum)
  rw [h] at s
  have p := mergeSort_perm (stable_le le) ((a :: l).enum)
  rw [h] at p
  refine ⟨l₁.map (·.2), l₂.map (·.2), ?_, ?_, ?_⟩
  · simpa using congrArg (·.map (·.2)) h
  · rw [← mergeSort_enum.go 1, ← map_append]
    congr 1
    have q : mergeSort (stable_le le) (enumFrom 1 l) ~ l₁ ++ l₂ :=
      (mergeSort_perm (stable_le le) (enumFrom 1 l)).trans
        (p.symm.trans perm_middle).cons_inv
    apply Perm.eq_of_sorted (le := stable_le le)
    · rintro ⟨i, a⟩ ⟨j, b⟩  ha hb
      simp only [mem_mergeSort] at ha
      simp only [← q.mem_iff, mem_mergeSort] at hb
      simp only [stable_le]
      simp only [Bool.if_false_right, Bool.and_eq_true, Prod.mk.injEq, and_imp]
      intro ab h ba h'
      simp only [Bool.decide_eq_true] at ba
      replace h : i ≤ j := by simpa [ab, ba] using h
      replace h' : j ≤ i := by simpa [ab, ba] using h'
      cases Nat.le_antisymm h h'
      constructor
      · rfl
      · have := mem_enumFrom ha
        have := mem_enumFrom hb
        simp_all
    · exact mergeSort_sorted (stable_le_trans trans) (stable_le_total total) ..
    · exact s.sublist ((sublist_cons_self (0, a) l₂).append_left l₁)
    · exact q
  · intro b m
    simp only [mem_map, Prod.exists, exists_eq_right] at m
    obtain ⟨j, m⟩ := m
    replace p := p.map (·.1)
    have nd' := nd.perm p.symm
    rw [map_append] at nd'
    have j0 := nd'.rel_of_mem_append
      (mem_map_of_mem (·.1) m) (mem_map_of_mem _ (mem_cons_self _ _))
    simp only [ne_eq] at j0
    have r := s.rel_of_mem_append m (mem_cons_self _ _)
    simp_all [stable_le]

/--
Another statement of stability of merge sort.
If `c` is a sorted sublist of `l`,
then `c` is still a sublist of `mergeSort le l`.
-/
theorem mergeSort_stable
    (trans : ∀ (a b c : α), le a b → le b c → le a c)
    (total : ∀ (a b : α), !le a b → le b a) :
    ∀ {c : List α} (_ : c.Sorted le) (_ : c <+ l),
    c <+ mergeSort le l
  | _, _, .slnil => nil_sublist _
  | c, hc, @Sublist.cons _ _ l a h => by
    obtain ⟨l₁, l₂, h₁, h₂, -⟩ := mergeSort_cons trans total a l
    rw [h₁]
    have h' := mergeSort_stable trans total hc h
    rw [h₂] at h'
    exact h'.middle a
  | _, _, @Sublist.cons₂ _ l₁ l₂ a h => by
    rename_i hc
    obtain ⟨l₃, l₄, h₁, h₂, h₃⟩ := mergeSort_cons trans total a l₂
    rw [h₁]
    have h' := mergeSort_stable trans total hc.tail h
    rw [h₂] at h'
    simp only [Bool.not_eq_true', tail_cons] at h₃ h'
    exact
      sublist_append_of_sublist_right (Sublist.cons₂ a
        ((fun w => Sublist.of_sublist_append_right w h') fun b m₁ m₃ =>
          (Bool.eq_not_self true).mp ((rel_of_pairwise_cons hc m₁).symm.trans (h₃ b m₃))))


/--
Another statement of stability of merge sort.
If a pair `[a, b]` is a sublist of `l` and `le a b`,
then `[a, b]` is still a sublist of `mergeSort le l`.
-/
theorem mergeSort_stable_pair
    (trans : ∀ (a b c : α), le a b → le b c → le a c)
    (total : ∀ (a b : α), !le a b → le b a)
    (hab : le a b) (h : [a, b] <+ l) : [a, b] <+ mergeSort le l :=
  mergeSort_stable trans total (pairwise_pair.mpr hab) h

end List

open List
