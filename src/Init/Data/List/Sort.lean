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

namespace mergeSort

abbrev Vec (α : Type) (n : Nat) := { l : List α // l.length = n }

def split (l : Vec α n) : Vec α ((n+1)/2) × Vec α (n/2) :=
  let r := splitAt ((n+1)/2) l.1
  (⟨r.1, by simp [r, splitAt_eq, l.2]; omega⟩, ⟨r.2, by simp [r, splitAt_eq, l.2]; omega⟩)

def merge (le : α → α → Bool) (l₁ l₂ : List α) : List α :=
  go l₁ l₂ []
where go : List α → List α → List α → List α
  | [], l₂, acc => acc.reverse ++ l₂
  | l₁, [], acc => acc.reverse ++ l₁
  | x :: xs, y :: ys, acc =>
    if le x y then
      go xs (y :: ys) (x :: acc)
    else
      go (x :: xs) ys (y :: acc)

end mergeSort

open mergeSort

def mergeSort (le : α → α → Bool) (l : List α) : List α :=
  run ⟨l, rfl⟩
where run : {n : Nat} → Vec α n → List α
  | 0, ⟨[], _⟩ => []
  | 1, ⟨[a], _⟩ => [a]
  | n+2, xs =>
    let (l, r) := split xs
    merge le (run l) (run r)

#eval mergeSort (· ≤ ·) [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]

#eval mergeSort (fun x y => x/10 ≤ y/10) [3, 100 + 1, 4, 100 + 1, 5, 100 + 9, 2, 10 + 6, 5, 10 + 3, 5]

abbrev Sorted (r : α → α → Bool) (xs : List α) : Prop := xs.Pairwise (fun x y => r x y)

namespace mergeSort

@[simp] theorem split_fst (l : Vec α n) : (split l).1 = ⟨l.1.take ((n+1)/2), by simp [split, splitAt_eq, l.2]; omega⟩ := by
  simp [split, splitAt_eq]

@[simp] theorem split_snd (l : Vec α n) : (split l).2 = ⟨l.1.drop ((n+1)/2), by simp [split, splitAt_eq, l.2]; omega⟩ := by
  simp [split, splitAt_eq]

theorem split_fst_append_split_snd (l : Vec α n) : (split l).1.1 ++ (split l).2.1 = l.1 := by
  simp

variable {le : α → α → Bool}

def naiveMerge (lt : α → α → Bool) : List α → List α → List α
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
    if lt x y then
      x :: naiveMerge lt xs (y :: ys)
    else
      y :: naiveMerge lt (x :: xs) ys

@[simp] theorem naiveMerge_nil_right (xs : List α) : naiveMerge le xs [] = xs := by
  induction xs with
  | nil => simp [naiveMerge]
  | cons x xs ih => simp [naiveMerge, ih]

theorem merge_go_eq_naiveMerge : merge.go le l₁ l₂ acc = acc.reverse ++ naiveMerge le l₁ l₂ := by
  induction l₁ generalizing l₂ acc with
  | nil => simp [merge.go, naiveMerge]
  | cons x l₁ ih₁ =>
    induction l₂ generalizing acc with
    | nil => simp [merge.go, naiveMerge]
    | cons y l₂ ih₂ =>
      simp [merge.go, naiveMerge]
      split <;> simp [ih₁, ih₂]

theorem merge_eq_naiveMerge : merge le l₁ l₂ = naiveMerge le l₁ l₂ := by
  simp [merge, merge_go_eq_naiveMerge]

def naiveMergeSort (le : α → α → Bool) : List α → List α
  | [] => []
  | [a] => [a]
  | a :: b :: xs =>
    let lr := split ⟨a :: b :: xs, rfl⟩
    have := by simpa using lr.2.2
    have := by simpa using lr.1.2
    naiveMerge le (naiveMergeSort le lr.1) (naiveMergeSort le lr.2)
termination_by l => l.length

theorem mergeSort_run_eq_naiveMergeSort : {n : Nat} → (l : Vec α n) → mergeSort.run le l = naiveMergeSort le l.1
  | 0, ⟨[], _⟩
  | 1, ⟨[a], _⟩ => by simp [run, naiveMergeSort]
  | n+2, ⟨a :: b :: l, h⟩ => by
    cases h
    simp [run, naiveMergeSort]
    rw [merge_eq_naiveMerge]
    rw [mergeSort_run_eq_naiveMergeSort, mergeSort_run_eq_naiveMergeSort]

theorem mergeSort_eq_naiveMergeSort : mergeSort le l = naiveMergeSort le l := by
  rw [mergeSort, mergeSort_run_eq_naiveMergeSort]

theorem mem_naiveMerge {a : α} {xs ys : List α} : a ∈ naiveMerge le xs ys ↔ a ∈ xs ∨ a ∈ ys := by
  induction xs generalizing ys with
  | nil => simp [naiveMerge]
  | cons x xs ih =>
    induction ys with
    | nil => simp [naiveMerge]
    | cons y ys ih =>
      simp only [naiveMerge]
      split <;> rename_i h
      · simp_all [or_assoc]
      · simp only [mem_cons, or_assoc, Bool.not_eq_true, ih, ← or_assoc]
        apply or_congr_left
        simp only [or_comm (a := a = y), or_assoc]

theorem naiveMerge_sorted
    (trans : ∀ {a b c : α}, le a b → le b c → le a c)
    (total : ∀ {a b : α}, !le a b → le b a)
    (l₁ l₂ : List α) (h₁ : l₁.Sorted le) (h₂ : l₂.Sorted le) : (naiveMerge le l₁ l₂).Sorted le := by
  induction l₁ generalizing l₂ with
  | nil => simpa only [naiveMerge]
  | cons x l₁ ih₁ =>
    induction l₂ with
    | nil => simpa only [naiveMerge]
    | cons y l₂ ih₂ =>
      simp only [naiveMerge]
      split <;> rename_i h
      · apply Pairwise.cons
        · intro z m
          rw [mem_naiveMerge, mem_cons] at m
          rcases m with (m|rfl|m)
          · exact rel_of_pairwise_cons h₁ m
          · exact h
          · exact trans h (rel_of_pairwise_cons h₂ m)
        · exact ih₁ _ h₁.tail h₂
      · apply Pairwise.cons
        · intro z m
          rw [mem_naiveMerge, mem_cons] at m
          rcases m with (⟨rfl|m⟩|m)
          · exact total (by simpa using h)
          · exact trans (total (by simpa using h)) (rel_of_pairwise_cons h₁ m)
          · exact rel_of_pairwise_cons h₂ m
        · exact ih₂ h₂.tail

theorem naiveMergeSort_sorted
    (trans : ∀ {a b c : α}, le a b → le b c → le a c)
    (total : ∀ {a b : α}, !le a b → le b a) :
    (l : List α) → (naiveMergeSort le l).Sorted le
  | [] => by simp [naiveMergeSort]
  | [a] => by simp [naiveMergeSort]
  | a :: b :: xs => by
    have : (split ⟨a :: b :: xs, rfl⟩).1.1.length < xs.length + 1 + 1 := by simp [split_fst]; omega
    have : (split ⟨a :: b :: xs, rfl⟩).2.1.length < xs.length + 1 + 1 := by simp [split_snd]; omega
    rw [naiveMergeSort]
    apply naiveMerge_sorted @trans @total
    apply naiveMergeSort_sorted trans total
    apply naiveMergeSort_sorted trans total
termination_by l => l.length

theorem split_fst_sorted (l : Vec α n) (h : Sorted le l) : Sorted le (split l).1 := by
  rw [split_fst]
  exact h.take

theorem split_snd_sorted (l : Vec α n) (h : Sorted le l) : Sorted le (split l).2 := by
  rw [split_snd]
  exact h.drop

theorem split_fst_le_split_snd {l : Vec α n} (h : Sorted le l) :
    ∀ a b, a ∈ (split l).1.1 → b ∈ (split l).2.1 → le a b := by
  rw [split_fst, split_snd]
  intro a b ma mb
  exact h.rel_of_mem_take_of_mem_drop ma mb

theorem naiveMerge_of_le : ∀ {xs ys : List α} (_ : ∀ a b, a ∈ xs → b ∈ ys → le a b),
    naiveMerge le xs ys = xs ++ ys
  | [], ys, _
  | xs, [], _ => by simp [naiveMerge]
  | x :: xs, y :: ys, h => by
    simp only [naiveMerge, cons_append]
    rw [if_pos, naiveMerge_of_le]
    · intro a b ma mb
      exact h a b (mem_cons_of_mem _ ma) mb
    · exact h x y (mem_cons_self _ _) (mem_cons_self _ _)

theorem naiveMergeSort_of_sorted : ∀ {l : List α} (_ : Sorted le l), naiveMergeSort le l = l
  | [], _ => by simp [naiveMergeSort]
  | [a], _ => by simp [naiveMergeSort]
  | a :: b :: xs, h => by
    have : (split ⟨a :: b :: xs, rfl⟩).1.1.length < xs.length + 1 + 1 := by simp [split_fst]; omega
    have : (split ⟨a :: b :: xs, rfl⟩).2.1.length < xs.length + 1 + 1 := by simp [split_snd]; omega
    rw [naiveMergeSort]
    rw [naiveMergeSort_of_sorted (split_fst_sorted ⟨a :: b :: xs, rfl⟩ h)]
    rw [naiveMergeSort_of_sorted (split_snd_sorted ⟨a :: b :: xs, rfl⟩ h)]
    rw [naiveMerge_of_le (split_fst_le_split_snd h)]
    rw [split_fst_append_split_snd]
termination_by l => l.length

def stable_le (le : α → α → Bool) (a b : Nat × α) : Bool :=
  if le a.2 b.2 then if le b.2 a.2 then a.1 ≤ b.1 else true else false

theorem split_cons_cons_enumFrom_fst (i : Nat) (l : List α) :
    (split ⟨(i, a) :: (i+1, b) :: l.enumFrom (i+2), rfl⟩).1.1 =
      (split ⟨a :: b :: l, rfl⟩).1.1.enumFrom i := by
  simp_all
  ext1 j
  rw [getElem?_take]
  rw [getElem?_enumFrom]
  rw [getElem?_cons]
  rw [take_cons (by omega), take_cons (α := α) (by omega), enumFrom_cons]
  congr 1
  induction l generalizing i with
  | nil => simp
  | cons c l ih =>
    simp
    rw [take_cons (by omega), take_cons (α := α) (by omega), enumFrom_cons]
    congr 1
    cases l with
    | nil => simp
    | cons d l =>

theorem split_cons_cons_enumFrom_snd (i : Nat) (l : List α) :
    (split ⟨(i, a) :: (i+1, b) :: l.enumFrom (i+2), rfl⟩).2.1 =
      (split ⟨a :: b :: l, rfl⟩).2.1.enumFrom (i+(l.length+3)/2) := by
  sorry

theorem naiveMerge_stable : ∀ (xs ys) (h : ∀ x y, x ∈ xs → y ∈ ys → x.1 ≤ y.1),
    (naiveMerge (stable_le le) xs ys).map (·.2) = naiveMerge le (xs.map (·.2)) (ys.map (·.2))
  | [], ys, _ => by simp [naiveMerge]
  | xs, [], _ => by simp [naiveMerge]
  | (i, x) :: xs, (j, y) :: ys, h => by
    simp only [naiveMerge, stable_le, map_cons]
    split <;> rename_i w
    · rw [if_pos]
      simp
      rw [naiveMerge_stable]
      rw [map_cons]
      sorry
      sorry
    · simp
      rw [naiveMerge_stable, map_cons]
      sorry

-- TODO: replace this with a proof via `Perm`
@[simp] theorem mem_naiveMergeSort {a : α} {l : List α} : a ∈ naiveMergeSort le l ↔ a ∈ l := by
  sorry

theorem naiveMergeSort_stable : ∀ {i : Nat} {l : List α},
    (naiveMergeSort (stable_le le) (l.enumFrom i)).map (·.2) = naiveMergeSort le l
  | _, []
  | _, [a] => by simp [naiveMergeSort]
  | _, a :: b :: xs => by
    have : (split ⟨a :: b :: xs, rfl⟩).1.1.length < xs.length + 1 + 1 := by simp [split_fst]; omega
    have : (split ⟨a :: b :: xs, rfl⟩).2.1.length < xs.length + 1 + 1 := by simp [split_snd]; omega
    simp only [naiveMergeSort, enumFrom]
    rw [split_cons_cons_enumFrom_fst]
    rw [split_cons_cons_enumFrom_snd]
    rw [naiveMerge_stable]
    · rw [naiveMergeSort_stable, naiveMergeSort_stable]
    · simp only [mem_naiveMergeSort, Prod.forall]
      intros j x k y mx my
      have := mem_enumFrom mx
      have := mem_enumFrom my
      simp_all
      omega
termination_by _ l => l.length

end mergeSort

theorem mergeSort_sorted
    (trans : ∀ {a b c : α}, le a b → le b c → le a c)
    (total : ∀ {a b : α}, !le a b → le b a)
    (l : List α) : (mergeSort le l).Sorted le := by
  rw [mergeSort_eq_naiveMergeSort]
  apply naiveMergeSort_sorted @trans @total

theorem mergeSort_of_sorted (h : Sorted le l) : mergeSort le l = l := by
  rw [mergeSort_eq_naiveMergeSort]
  apply naiveMergeSort_of_sorted h

/--
This merge sort algorithm is "stable",
in the sense that breaking ties in the ordering function using the position in the list
has no effect on the output.

That is, elements which are equal with respect to the ordering function will remain
in the same order in the output list as they were in the input list.
-/
theorem mergeSort_stable {l : List α} :
    let stable_le := fun a b => if le a.2 b.2 then if le b.2 a.2 then a.1 ≤ b.1 else true else false
    (mergeSort stable_le l.enum).map (·.2) = mergeSort le l := by
  dsimp [stable_le]
  rw [mergeSort_eq_naiveMergeSort, mergeSort_eq_naiveMergeSort]
  erw [naiveMergeSort_stable] -- `erw` here to make the `stable_le` definitions match

end List

open List

-- #time
-- #eval (mergeSort (· ≤ ·) (iota (10^7))).length
