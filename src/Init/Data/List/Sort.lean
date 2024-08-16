import Lean

namespace List

def splitAt (n : Nat) (l : List α) : List α × List α := go l n [] where
  /-- Auxiliary for `splitAt`: `splitAt.go xs n acc = (acc.reverse ++ take n xs, drop n xs)`
  if `n < length xs`, else `(l, [])`. -/
  go : List α → Nat → List α → List α × List α
  | x :: xs, n+1, acc => go xs n (x :: acc)
  | xs, _, acc => (acc.reverse, xs)

theorem splitAt_go (n : Nat) (l acc : List α) :
    splitAt.go l n acc = (acc.reverse ++ l.take n, l.drop n) := by
  induction l generalizing n acc with
  | nil => simp [splitAt.go]
  | cons x xs ih =>
    cases n with
    | zero => simp [splitAt.go]
    | succ n =>
      rw [splitAt.go, take_succ_cons, drop_succ_cons, ih n (x :: acc),
        reverse_cons, append_assoc, singleton_append]

theorem splitAt_eq (n : Nat) (l : List α) : splitAt n l = (l.take n, l.drop n) := by
  rw [splitAt, splitAt_go, reverse_nil, nil_append]

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
`O(|l| + |r|)`. Merge two lists using `le` as a switch.
-/
def mergeTR (le : α → α → Bool) (l₁ l₂ : List α) : List α :=
  go l₁ l₂ []
where go : List α → List α → List α → List α
  | [], l₂, acc => reverseAux acc l₂
  | l₁, [], acc => reverseAux acc l₁
  | x :: xs, y :: ys, acc =>
    if le x y then
      go xs (y :: ys) (x :: acc)
    else
      go (x :: xs) ys (y :: acc)

/--
Split a list in two equal parts. If the length is odd, the first part will be one element longer.
-/
def splitInTwo (l : { l : List α // l.length = n }) :
    { l : List α // l.length = (n+1)/2 } × { l : List α // l.length = n/2 } :=
  let r := splitAt ((n+1)/2) l.1
  (⟨r.1, by simp [r, splitAt_eq, l.2]; omega⟩, ⟨r.2, by simp [r, splitAt_eq, l.2]; omega⟩)

/--
Simplified implementation of stable merge sort.

This version uses the non tail-recursive `merge` function,
and so is not suitable for large lists, but is straightforward to reason about.
It is replaced at runtime by `mergeSortTR` using a `@[csimp]` lemma.
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

def mergeSortTR (le : α → α → Bool) (l : List α) : List α :=
  run ⟨l, rfl⟩
where run : {n : Nat} → { l : List α // l.length = n } → List α
  | 0, ⟨[], _⟩ => []
  | 1, ⟨[a], _⟩ => [a]
  | n+2, xs =>
    let (l, r) := splitInTwo xs
    mergeTR le (run l) (run r)

#eval mergeSortTR (· ≤ ·) [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]

#eval mergeSortTR (fun x y => x/10 ≤ y/10) [3, 100 + 1, 4, 100 + 1, 5, 100 + 9, 2, 10 + 6, 5, 10 + 3, 5]

abbrev Sorted (r : α → α → Bool) (xs : List α) : Prop := xs.Pairwise (fun x y => r x y)

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

theorem mergeTR_go_eq : mergeTR.go le l₁ l₂ acc = acc.reverse ++ merge le l₁ l₂ := by
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

theorem mergeSortTR_run_eq_mergeSort : {n : Nat} → (l : { l : List α // l.length = n }) → mergeSortTR.run le l = mergeSort le l.1
  | 0, ⟨[], _⟩
  | 1, ⟨[a], _⟩ => by simp [mergeSortTR.run, mergeSort]
  | n+2, ⟨a :: b :: l, h⟩ => by
    cases h
    simp [mergeSortTR.run, mergeSort]
    rw [merge_eq_mergeTR]
    rw [mergeSortTR_run_eq_mergeSort, mergeSortTR_run_eq_mergeSort]

@[csimp] theorem mergeSort_eq_mergeSortTR : @mergeSort = @mergeSortTR := by
  funext
  rw [mergeSortTR, mergeSortTR_run_eq_mergeSort]

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
    (trans : ∀ {a b c : α}, le a b → le b c → le a c)
    (total : ∀ {a b : α}, !le a b → le b a)
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
          · exact trans h (rel_of_pairwise_cons h₂ m)
        · exact ih₁ _ h₁.tail h₂
      · apply Pairwise.cons
        · intro z m
          rw [mem_merge, mem_cons] at m
          rcases m with (⟨rfl|m⟩|m)
          · exact total (by simpa using h)
          · exact trans (total (by simpa using h)) (rel_of_pairwise_cons h₁ m)
          · exact rel_of_pairwise_cons h₂ m
        · exact ih₂ h₂.tail

theorem splitInTwo_fst_sorted (l : { l : List α // l.length = n }) (h : Sorted le l) : Sorted le (splitInTwo l).1 := by
  rw [splitInTwo_fst]
  exact h.take

theorem splitInTwo_snd_sorted (l : { l : List α // l.length = n }) (h : Sorted le l) : Sorted le (splitInTwo l).2 := by
  rw [splitInTwo_snd]
  exact h.drop

theorem splitInTwo_fst_le_splitInTwo_snd {l : { l : List α // l.length = n }} (h : Sorted le l) :
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

theorem mergeSort_perm : ∀ {l : List α}, mergeSort le l ~ l
  | [] => by simp [mergeSort]
  | [a] => by simp [mergeSort]
  | a :: b :: xs => by
    simp only [mergeSort]
    have : (splitInTwo ⟨a :: b :: xs, rfl⟩).1.1.length < xs.length + 1 + 1 := by simp [splitInTwo_fst]; omega
    have : (splitInTwo ⟨a :: b :: xs, rfl⟩).2.1.length < xs.length + 1 + 1 := by simp [splitInTwo_snd]; omega
    exact merge_perm_append.trans
      ((mergeSort_perm.append mergeSort_perm).trans
        (Perm.of_eq (splitInTwo_fst_append_splitInTwo_snd _)))
termination_by l => l.length

@[simp] theorem mem_mergeSort {a : α} {l : List α} : a ∈ mergeSort le l ↔ a ∈ l :=
  mergeSort_perm.mem_iff

/--
The result of `mergeSort` is sorted,
as long as the comparison function is transitive (`le a b → le b c → le a c`)
and total in the sense that `le a b ∨ le b a`.

The comparison function need not be irreflexive, i.e. `le a b` and `le b a` is allowed even when `a ≠ b`.
-/
theorem mergeSort_sorted
    (trans : ∀ {a b c : α}, le a b → le b c → le a c)
    (total : ∀ {a b : α}, !le a b → le b a) :
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
* `mergeSort_stable_pair`: if `[a, b] <+ l` and `le a b`, then `[a, b] <+ mergeSort le l`)
* `mergeSort_stable_sublist`: if `c <+ l` and `c.Pairwise le`, then `c <+ mergeSort le l`.
-/
theorem mergeSort_stable : ∀ {i : Nat} {l : List α},
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
    · rw [mergeSort_stable, mergeSort_stable]
    · simp only [mem_mergeSort, Prod.forall]
      intros j x k y mx my
      have := mem_enumFrom mx
      have := mem_enumFrom my
      simp_all
      omega
termination_by _ l => l.length

theorem mergeSort_cons (le) : ∀ (a : α) (l : List α),
    ∃ l₁ l₂, mergeSort le (a :: l) = l₁ ++ a :: l₂ ∧ mergeSort le l = l₁ ++ l₂ ∧
      ∀ b, b ∈ l₁ → !le a b
  | a, [] => by
    simp only [mergeSort]
    exact ⟨[], [], by simp⟩
  | a, b :: l => by
    simp [mergeSort]
    rw [take_cons]
    rw [h₁, h₂]
    exact ⟨a :: l₁, l₂, rfl, rfl, fun b m => h₃ _ (mem_cons_of_mem _ m)⟩


/--
Another statement of stability of merge sort.
If `c` is a sorted sublist of `l`,
then `c` is still a sublist of `mergeSort le l`.
-/
theorem mergeSort_stable_sublist : ∀ {c : List α} (_ : c.Sorted le) (_ : c <+ l),
    c <+ mergeSort le l
  | _, _, .slnil => nil_sublist _
  | c, hc, @Sublist.cons _ _ l a h => by
    obtain ⟨l₁, l₂, h₁, h₂, -⟩ := mergeSort_cons le a l
    rw [h₁]
    have h' := mergeSort_stable_sublist hc h
    rw [h₂] at h'
    exact h'.middle a
  | _, _, @Sublist.cons₂ _ l₁ l₂ a h => by
    rename_i hc
    obtain ⟨l₃, l₄, h₁, h₂, h₃⟩ := mergeSort_cons le a l₂
    rw [h₁]
    have h' := mergeSort_stable_sublist hc.tail h
    rw [h₂] at h'
    simp at h₃ h'
    apply sublist_append_of_sublist_right
    apply Sublist.cons₂ a
    apply h'.of_sublist_append_right
    intro b m₁ m₃
    specialize h₃ _ m₃
    have := rel_of_pairwise_cons hc m₁
    simp_all

/--
Another statement of stability of merge sort.
If a pair `[a, b]` is a sublist of `l` and `le a b`,
then `[a, b]` is still a sublist of `mergeSort le l`.
-/
theorem mergeSort_stable_pair (hab : le a b) (h : [a, b] <+ l) : [a, b] <+ mergeSort le l :=
  mergeSort_stable_sublist (pairwise_pair.mpr hab) h

end List

open List

-- #time
-- #eval (mergeSort (· ≤ ·) (iota (10^6))).length
