/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
prelude
import Init.Data.List.Zip
import Init.Data.List.Sublist
import Init.Data.List.Find
import Init.Data.Nat.Lemmas

/-!
# Further lemmas about `List.take`, `List.drop`, `List.zip` and `List.zipWith`.

These are in a separate file from most of the list lemmas
as they required importing more lemmas about natural numbers, and use `omega`.
-/

namespace List

open Nat

/-! ### take -/

@[simp] theorem length_take : ∀ (i : Nat) (l : List α), length (take i l) = min i (length l)
  | 0, l => by simp [Nat.zero_min]
  | succ n, [] => by simp [Nat.min_zero]
  | succ n, _ :: l => by simp [Nat.succ_min_succ, length_take]

theorem length_take_le (n) (l : List α) : length (take n l) ≤ n := by simp [Nat.min_le_left]

theorem length_take_le' (n) (l : List α) : length (take n l) ≤ l.length :=
  by simp [Nat.min_le_right]

theorem length_take_of_le (h : n ≤ length l) : length (take n l) = n := by simp [Nat.min_eq_left h]

/-- The `i`-th element of a list coincides with the `i`-th element of any of its prefixes of
length `> i`. Version designed to rewrite from the big list to the small list. -/
theorem getElem_take' (L : List α) {i j : Nat} (hi : i < L.length) (hj : i < j) :
    L[i] = (L.take j)[i]'(length_take .. ▸ Nat.lt_min.mpr ⟨hj, hi⟩) :=
  getElem_of_eq (take_append_drop j L).symm _ ▸ getElem_append_left ..

/-- The `i`-th element of a list coincides with the `i`-th element of any of its prefixes of
length `> i`. Version designed to rewrite from the small list to the big list. -/
@[simp] theorem getElem_take (L : List α) {j i : Nat} {h : i < (L.take j).length} :
    (L.take j)[i] =
    L[i]'(Nat.lt_of_lt_of_le h (length_take_le' _ _)) := by
  rw [length_take, Nat.lt_min] at h; rw [getElem_take' L _ h.1]

theorem getElem?_take_eq_none {l : List α} {n m : Nat} (h : n ≤ m) :
    (l.take n)[m]? = none :=
  getElem?_eq_none <| Nat.le_trans (length_take_le _ _) h

theorem getElem?_take {l : List α} {n m : Nat} :
    (l.take n)[m]? = if m < n then l[m]? else none := by
  split
  · next h => exact getElem?_take_of_lt h
  · next h => exact getElem?_take_eq_none (Nat.le_of_not_lt h)

theorem head?_take {l : List α} {n : Nat} :
    (l.take n).head? = if n = 0 then none else l.head? := by
  simp [head?_eq_getElem?, getElem?_take]
  split
  · rw [if_neg (by omega)]
  · rw [if_pos (by omega)]

theorem head_take {l : List α} {n : Nat} (h : l.take n ≠ []) :
    (l.take n).head h = l.head (by simp_all) := by
  apply Option.some_inj.1
  rw [← head?_eq_head, ← head?_eq_head, head?_take, if_neg]
  simp_all

theorem getLast?_take {l : List α} : (l.take n).getLast? = if n = 0 then none else l[n - 1]?.or l.getLast? := by
  rw [getLast?_eq_getElem?, getElem?_take, length_take]
  split
  · rw [if_neg (by omega)]
    rw [Nat.min_def]
    split
    · rw [getElem?_eq_getElem (by omega)]
      simp
    · rw [← getLast?_eq_getElem?, getElem?_eq_none (by omega)]
      simp
  · rw [if_pos]
    omega

theorem getLast_take {l : List α} (h : l.take n ≠ []) :
    (l.take n).getLast h = l[n - 1]?.getD (l.getLast (by simp_all)) := by
  rw [getLast_eq_getElem, getElem_take]
  simp [length_take, Nat.min_def]
  simp at h
  split
  · rw [getElem?_eq_getElem (by omega)]
    simp
  · rw [getElem?_eq_none (by omega), getLast_eq_getElem]
    simp

theorem take_take : ∀ (n m) (l : List α), take n (take m l) = take (min n m) l
  | n, 0, l => by rw [Nat.min_zero, take_zero, take_nil]
  | 0, m, l => by rw [Nat.zero_min, take_zero, take_zero]
  | succ n, succ m, nil => by simp only [take_nil]
  | succ n, succ m, a :: l => by
    simp only [take, succ_min_succ, take_take n m l]

theorem take_set_of_le (a : α) {n m : Nat} (l : List α) (h : m ≤ n) :
    (l.set n a).take m = l.take m :=
  List.ext_getElem? fun i => by
    rw [getElem?_take, getElem?_take]
    split
    · next h' => rw [getElem?_set_ne (by omega)]
    · rfl

@[deprecated take_set_of_le (since := "2025-02-04")]
abbrev take_set_of_lt := @take_set_of_le

@[simp] theorem take_replicate (a : α) : ∀ n m : Nat, take n (replicate m a) = replicate (min n m) a
  | n, 0 => by simp [Nat.min_zero]
  | 0, m => by simp [Nat.zero_min]
  | succ n, succ m => by simp [replicate_succ, succ_min_succ, take_replicate]

@[simp] theorem drop_replicate (a : α) : ∀ n m : Nat, drop n (replicate m a) = replicate (m - n) a
  | n, 0 => by simp
  | 0, m => by simp
  | succ n, succ m => by simp [replicate_succ, succ_sub_succ, drop_replicate]

/-- Taking the first `n` elements in `l₁ ++ l₂` is the same as appending the first `n` elements
of `l₁` to the first `n - l₁.length` elements of `l₂`. -/
theorem take_append_eq_append_take {l₁ l₂ : List α} {n : Nat} :
    take n (l₁ ++ l₂) = take n l₁ ++ take (n - l₁.length) l₂ := by
  induction l₁ generalizing n
  · simp
  · cases n
    · simp [*]
    · simp only [cons_append, take_succ_cons, length_cons, succ_eq_add_one, cons.injEq,
        append_cancel_left_eq, true_and, *]
      congr 1
      omega

theorem take_append_of_le_length {l₁ l₂ : List α} {n : Nat} (h : n ≤ l₁.length) :
    (l₁ ++ l₂).take n = l₁.take n := by
  simp [take_append_eq_append_take, Nat.sub_eq_zero_of_le h]

/-- Taking the first `l₁.length + i` elements in `l₁ ++ l₂` is the same as appending the first
`i` elements of `l₂` to `l₁`. -/
theorem take_append {l₁ l₂ : List α} (i : Nat) :
    take (l₁.length + i) (l₁ ++ l₂) = l₁ ++ take i l₂ := by
  rw [take_append_eq_append_take, take_of_length_le (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

@[simp]
theorem take_eq_take :
    ∀ {l : List α} {m n : Nat}, l.take m = l.take n ↔ min m l.length = min n l.length
  | [], m, n => by simp [Nat.min_zero]
  | _ :: xs, 0, 0 => by simp
  | x :: xs, m + 1, 0 => by simp [Nat.zero_min, succ_min_succ]
  | x :: xs, 0, n + 1 => by simp [Nat.zero_min, succ_min_succ]
  | x :: xs, m + 1, n + 1 => by simp [succ_min_succ, take_eq_take]

theorem take_add (l : List α) (m n : Nat) : l.take (m + n) = l.take m ++ (l.drop m).take n := by
  suffices take (m + n) (take m l ++ drop m l) = take m l ++ take n (drop m l) by
    rw [take_append_drop] at this
    assumption
  rw [take_append_eq_append_take, take_of_length_le, append_right_inj]
  · simp only [take_eq_take, length_take, length_drop]
    omega
  apply Nat.le_trans (m := m)
  · apply length_take_le
  · apply Nat.le_add_right

theorem take_one {l : List α} : l.take 1 = l.head?.toList := by
  induction l <;> simp

theorem take_eq_append_getElem_of_pos {n} {l : List α} (h₁ : 0 < n) (h₂ : n < l.length) : l.take n = l.take (n - 1) ++ [l[n - 1]] :=
  match n, h₁ with
  | n + 1, _ => take_succ_eq_append_getElem (n := n) (by omega)

theorem dropLast_take {n : Nat} {l : List α} (h : n < l.length) :
    (l.take n).dropLast = l.take (n - 1) := by
  simp only [dropLast_eq_take, length_take, Nat.le_of_lt h, Nat.min_eq_left, take_take, sub_le]

@[deprecated map_eq_append_iff (since := "2024-09-05")] abbrev map_eq_append_split := @map_eq_append_iff

theorem take_eq_dropLast {l : List α} {i : Nat} (h : i + 1 = l.length) :
    l.take i = l.dropLast := by
  induction l generalizing i with
  | nil => simp
  | cons a as ih =>
    cases i
    · simp_all
    · cases as with
      | nil => simp_all
      | cons b bs =>
        simp only [take_succ_cons, dropLast_cons₂]
        rw [ih]
        simpa using h

theorem take_prefix_take_left (l : List α) {m n : Nat} (h : m ≤ n) : take m l <+: take n l := by
  rw [isPrefix_iff]
  intro i w
  rw [getElem?_take_of_lt, getElem_take, getElem?_eq_getElem]
  simp only [length_take] at w
  exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le w (Nat.min_le_left _ _)) h

theorem take_sublist_take_left (l : List α) {m n : Nat} (h : m ≤ n) : take m l <+ take n l :=
  (take_prefix_take_left l h).sublist

theorem take_subset_take_left (l : List α) {m n : Nat} (h : m ≤ n) : take m l ⊆ take n l :=
  (take_sublist_take_left l h).subset

/-! ### drop -/

theorem lt_length_drop (L : List α) {i j : Nat} (h : i + j < L.length) : j < (L.drop i).length := by
  have A : i < L.length := Nat.lt_of_le_of_lt (Nat.le.intro rfl) h
  rw [(take_append_drop i L).symm] at h
  simpa only [Nat.le_of_lt A, Nat.min_eq_left, Nat.add_lt_add_iff_left, length_take,
    length_append] using h

/-- The `i + j`-th element of a list coincides with the `j`-th element of the list obtained by
dropping the first `i` elements. Version designed to rewrite from the big list to the small list. -/
theorem getElem_drop' (L : List α) {i j : Nat} (h : i + j < L.length) :
    L[i + j] = (L.drop i)[j]'(lt_length_drop L h) := by
  have : i ≤ L.length := Nat.le_trans (Nat.le_add_right _ _) (Nat.le_of_lt h)
  rw [getElem_of_eq (take_append_drop i L).symm h, getElem_append_right]
  · simp [Nat.min_eq_left this, Nat.add_sub_cancel_left]
  · simp [Nat.min_eq_left this, Nat.le_add_right]

/-- The `i + j`-th element of a list coincides with the `j`-th element of the list obtained by
dropping the first `i` elements. Version designed to rewrite from the small list to the big list. -/
@[simp] theorem getElem_drop (L : List α) {i : Nat} {j : Nat} {h : j < (L.drop i).length} :
    (L.drop i)[j] = L[i + j]'(by
      rw [Nat.add_comm]
      exact Nat.add_lt_of_lt_sub (length_drop i L ▸ h)) := by
  rw [getElem_drop']

@[simp]
theorem getElem?_drop (L : List α) (i j : Nat) : (L.drop i)[j]? = L[i + j]? := by
  ext
  simp only [getElem?_eq_some_iff, getElem_drop, Option.mem_def]
  constructor <;> intro ⟨h, ha⟩
  · exact ⟨_, ha⟩
  · refine ⟨?_, ha⟩
    rw [length_drop]
    rw [Nat.add_comm] at h
    apply Nat.lt_sub_of_add_lt h

theorem mem_take_iff_getElem {l : List α} {a : α} :
    a ∈ l.take n ↔ ∃ (i : Nat) (hm : i < min n l.length), l[i] = a := by
  rw [mem_iff_getElem]
  constructor
  · rintro ⟨i, hm, rfl⟩
    simp at hm
    refine ⟨i, by omega, by rw [getElem_take]⟩
  · rintro ⟨i, hm, rfl⟩
    refine ⟨i, by simpa, by rw [getElem_take]⟩

theorem mem_drop_iff_getElem {l : List α} {a : α} :
    a ∈ l.drop n ↔ ∃ (i : Nat) (hm : i + n < l.length), l[n + i] = a := by
  rw [mem_iff_getElem]
  constructor
  · rintro ⟨i, hm, rfl⟩
    simp at hm
    refine ⟨i, by omega, by rw [getElem_drop]⟩
  · rintro ⟨i, hm, rfl⟩
    refine ⟨i, by simp; omega, by rw [getElem_drop]⟩

@[simp] theorem head?_drop (l : List α) (n : Nat) :
    (l.drop n).head? = l[n]? := by
  rw [head?_eq_getElem?, getElem?_drop, Nat.add_zero]

@[simp] theorem head_drop {l : List α} {n : Nat} (h : l.drop n ≠ []) :
    (l.drop n).head h = l[n]'(by simp_all) := by
  have w : n < l.length := length_lt_of_drop_ne_nil h
  simp [getElem?_eq_getElem, h, w, head_eq_iff_head?_eq_some]

theorem getLast?_drop {l : List α} : (l.drop n).getLast? = if l.length ≤ n then none else l.getLast? := by
  rw [getLast?_eq_getElem?, getElem?_drop]
  rw [length_drop]
  split
  · rw [getElem?_eq_none (by omega)]
  · rw [getLast?_eq_getElem?]
    congr
    omega

@[simp] theorem getLast_drop {l : List α} (h : l.drop n ≠ []) :
    (l.drop n).getLast h = l.getLast (ne_nil_of_length_pos (by simp at h; omega)) := by
  simp only [ne_eq, drop_eq_nil_iff] at h
  apply Option.some_inj.1
  simp only [← getLast?_eq_getLast, getLast?_drop, ite_eq_right_iff]
  omega

theorem drop_length_cons {l : List α} (h : l ≠ []) (a : α) :
    (a :: l).drop l.length = [l.getLast h] := by
  induction l generalizing a with
  | nil =>
    cases h rfl
  | cons y l ih =>
    simp only [drop, length]
    by_cases h₁ : l = []
    · simp [h₁]
    rw [getLast_cons h₁]
    exact ih h₁ y

/-- Dropping the elements up to `n` in `l₁ ++ l₂` is the same as dropping the elements up to `n`
in `l₁`, dropping the elements up to `n - l₁.length` in `l₂`, and appending them. -/
theorem drop_append_eq_append_drop {l₁ l₂ : List α} {n : Nat} :
    drop n (l₁ ++ l₂) = drop n l₁ ++ drop (n - l₁.length) l₂ := by
  induction l₁ generalizing n
  · simp
  · cases n
    · simp [*]
    · simp only [cons_append, drop_succ_cons, length_cons, succ_eq_add_one, append_cancel_left_eq, *]
      congr 1
      omega

theorem drop_append_of_le_length {l₁ l₂ : List α} {n : Nat} (h : n ≤ l₁.length) :
    (l₁ ++ l₂).drop n = l₁.drop n ++ l₂ := by
  simp [drop_append_eq_append_drop, Nat.sub_eq_zero_of_le h]

/-- Dropping the elements up to `l₁.length + i` in `l₁ + l₂` is the same as dropping the elements
up to `i` in `l₂`. -/
@[simp]
theorem drop_append {l₁ l₂ : List α} (i : Nat) : drop (l₁.length + i) (l₁ ++ l₂) = drop i l₂ := by
  rw [drop_append_eq_append_drop, drop_eq_nil_of_le] <;>
    simp [Nat.add_sub_cancel_left, Nat.le_add_right]

theorem set_eq_take_append_cons_drop (l : List α) (n : Nat) (a : α) :
    l.set n a = if n < l.length then l.take n ++ a :: l.drop (n + 1) else l := by
  split <;> rename_i h
  · ext1 m
    by_cases h' : m < n
    · rw [getElem?_append_left (by simp [length_take]; omega), getElem?_set_ne (by omega),
        getElem?_take_of_lt h']
    · by_cases h'' : m = n
      · subst h''
        rw [getElem?_set_self ‹_›, getElem?_append_right, length_take,
          Nat.min_eq_left (by omega), Nat.sub_self, getElem?_cons_zero]
        rw [length_take]
        exact Nat.min_le_left m l.length
      · have h''' : n < m := by omega
        rw [getElem?_set_ne (by omega), getElem?_append_right, length_take,
          Nat.min_eq_left (by omega)]
        · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h'''
          have p : n + k + 1 - n = k + 1 := by omega
          rw [p]
          rw [getElem?_cons_succ, getElem?_drop]
          congr 1
          omega
        · rw [length_take]
          exact Nat.le_trans (Nat.min_le_left _ _) (by omega)
  · rw [set_eq_of_length_le]
    omega

theorem exists_of_set {n : Nat} {a' : α} {l : List α} (h : n < l.length) :
    ∃ l₁ l₂, l = l₁ ++ l[n] :: l₂ ∧ l₁.length = n ∧ l.set n a' = l₁ ++ a' :: l₂ := by
  refine ⟨l.take n, l.drop (n + 1), ⟨by simp, ⟨length_take_of_le (Nat.le_of_lt h), ?_⟩⟩⟩
  simp [set_eq_take_append_cons_drop, h]

theorem drop_set_of_lt (a : α) {n m : Nat} (l : List α)
    (hnm : n < m) : drop m (l.set n a) = l.drop m :=
  ext_getElem? fun k => by simpa only [getElem?_drop] using getElem?_set_ne (by omega)

theorem drop_take : ∀ (m n : Nat) (l : List α), drop n (take m l) = take (m - n) (drop n l)
  | 0, _, _ => by simp
  | _, 0, _ => by simp
  | _, _, [] => by simp
  | m+1, n+1, h :: t => by
    simp [take_succ_cons, drop_succ_cons, drop_take m n t]
    congr 1
    omega

@[simp] theorem drop_take_self : drop n (take n l) = [] := by
  rw [drop_take]
  simp

theorem take_reverse {α} {xs : List α} {n : Nat} :
    xs.reverse.take n = (xs.drop (xs.length - n)).reverse := by
  by_cases h : n ≤ xs.length
  · induction xs generalizing n <;>
      simp only [reverse_cons, drop, reverse_nil, Nat.zero_sub, length, take_nil]
    next xs_hd xs_tl xs_ih =>
    cases Nat.lt_or_eq_of_le h with
    | inl h' =>
      have h' := Nat.le_of_succ_le_succ h'
      rw [take_append_of_le_length, xs_ih h']
      rw [show xs_tl.length + 1 - n = succ (xs_tl.length - n) from _, drop]
      · rwa [succ_eq_add_one, Nat.sub_add_comm]
      · rwa [length_reverse]
    | inr h' =>
      subst h'
      rw [length, Nat.sub_self, drop]
      suffices xs_tl.length + 1 = (xs_tl.reverse ++ [xs_hd]).length by
        rw [this, take_length, reverse_cons]
      rw [length_append, length_reverse]
      rfl
  · have w : xs.length - n = 0 := by omega
    rw [take_of_length_le, w, drop_zero]
    simp
    omega

theorem drop_reverse {α} {xs : List α} {n : Nat} :
    xs.reverse.drop n = (xs.take (xs.length - n)).reverse := by
  by_cases h : n ≤ xs.length
  · conv =>
      rhs
      rw [← reverse_reverse xs]
    rw [← reverse_reverse xs] at h
    generalize xs.reverse = xs' at h ⊢
    rw [take_reverse]
    · simp only [length_reverse, reverse_reverse] at *
      congr
      omega
  · have w : xs.length - n = 0 := by omega
    rw [drop_of_length_le, w, take_zero, reverse_nil]
    simp
    omega

theorem reverse_take {l : List α} {n : Nat} :
    (l.take n).reverse = l.reverse.drop (l.length - n) := by
  by_cases h : n ≤ l.length
  · rw [drop_reverse]
    congr
    omega
  · have w : l.length - n = 0 := by omega
    rw [w, drop_zero, take_of_length_le]
    omega

theorem reverse_drop {l : List α} {n : Nat} :
    (l.drop n).reverse = l.reverse.take (l.length - n) := by
  by_cases h : n ≤ l.length
  · rw [take_reverse]
    congr
    omega
  · have w : l.length - n = 0 := by omega
    rw [w, take_zero, drop_of_length_le, reverse_nil]
    omega

theorem take_add_one {l : List α} {n : Nat} :
    l.take (n + 1) = l.take n ++ l[n]?.toList := by
  simp [take_add, take_one]

theorem drop_eq_getElem?_toList_append {l : List α} {n : Nat} :
    l.drop n = l[n]?.toList ++ l.drop (n + 1) := by
  induction l generalizing n with
  | nil => simp
  | cons hd tl ih =>
    cases n
    · simp
    · simp only [drop_succ_cons, getElem?_cons_succ]
      rw [ih]

theorem drop_sub_one {l : List α} {n : Nat} (h : 0 < n) :
    l.drop (n - 1) = l[n - 1]?.toList ++ l.drop n := by
  rw [drop_eq_getElem?_toList_append]
  congr
  omega

/-! ### findIdx -/

theorem false_of_mem_take_findIdx {xs : List α} {p : α → Bool} (h : x ∈ xs.take (xs.findIdx p)) :
    p x = false := by
  simp only [mem_take_iff_getElem, forall_exists_index] at h
  obtain ⟨i, h, rfl⟩ := h
  exact not_of_lt_findIdx (by omega)

@[simp] theorem findIdx_take {xs : List α} {n : Nat} {p : α → Bool} :
    (xs.take n).findIdx p = min n (xs.findIdx p) := by
  induction xs generalizing n with
  | nil => simp
  | cons x xs ih =>
    cases n
    · simp
    · simp only [take_succ_cons, findIdx_cons, ih, cond_eq_if]
      split
      · simp
      · rw [Nat.add_min_add_right]

@[simp] theorem findIdx?_take {xs : List α} {n : Nat} {p : α → Bool} :
    (xs.take n).findIdx? p = (xs.findIdx? p).bind (Option.guard (fun i => i < n)) := by
  induction xs generalizing n with
  | nil => simp
  | cons x xs ih =>
    cases n
    · simp
    · simp only [take_succ_cons, findIdx?_cons]
      split
      · simp
      · simp [ih, Option.guard_comp, Option.bind_map]

@[simp] theorem min_findIdx_findIdx {xs : List α} {p q : α → Bool} :
    min (xs.findIdx p) (xs.findIdx q) = xs.findIdx (fun a => p a || q a) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp [findIdx_cons, cond_eq_if, Bool.not_eq_eq_eq_not, Bool.not_true]
    split <;> split <;> simp_all [Nat.add_min_add_right]

/-! ### takeWhile -/

theorem takeWhile_eq_take_findIdx_not {xs : List α} {p : α → Bool} :
    takeWhile p xs = take (xs.findIdx (fun a => !p a)) xs := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [takeWhile_cons, ih, findIdx_cons, cond_eq_if, Bool.not_eq_eq_eq_not, Bool.not_true]
    split <;> simp_all

theorem dropWhile_eq_drop_findIdx_not {xs : List α} {p : α → Bool} :
    dropWhile p xs = drop (xs.findIdx (fun a => !p a)) xs := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [dropWhile_cons, ih, findIdx_cons, cond_eq_if, Bool.not_eq_eq_eq_not, Bool.not_true]
    split <;> simp_all

/-! ### rotateLeft -/

@[simp] theorem rotateLeft_replicate (n) (a : α) : rotateLeft (replicate m a) n = replicate m a := by
  cases n with
  | zero => simp
  | succ n =>
    suffices 1 < m → m - (n + 1) % m + min ((n + 1) % m) m = m by
      simpa [rotateLeft]
    intro h
    rw [Nat.min_eq_left (Nat.le_of_lt (Nat.mod_lt _ (by omega)))]
    have : (n + 1) % m < m := Nat.mod_lt _ (by omega)
    omega

/-! ### rotateRight -/

@[simp] theorem rotateRight_replicate (n) (a : α) : rotateRight (replicate m a) n = replicate m a := by
  cases n with
  | zero => simp
  | succ n =>
    suffices 1 < m → m - (m - (n + 1) % m) + min (m - (n + 1) % m) m = m by
      simpa [rotateRight]
    intro h
    have : (n + 1) % m < m := Nat.mod_lt _ (by omega)
    rw [Nat.min_eq_left (by omega)]
    omega

/-! ### zipWith -/

@[simp] theorem length_zipWith (f : α → β → γ) (l₁ l₂) :
    length (zipWith f l₁ l₂) = min (length l₁) (length l₂) := by
  induction l₁ generalizing l₂ <;> cases l₂ <;>
    simp_all [succ_min_succ, Nat.zero_min, Nat.min_zero]

theorem lt_length_left_of_zipWith {f : α → β → γ} {i : Nat} {l : List α} {l' : List β}
    (h : i < (zipWith f l l').length) : i < l.length := by rw [length_zipWith] at h; omega

theorem lt_length_right_of_zipWith {f : α → β → γ} {i : Nat} {l : List α} {l' : List β}
    (h : i < (zipWith f l l').length) : i < l'.length := by rw [length_zipWith] at h; omega

@[simp]
theorem getElem_zipWith {f : α → β → γ} {l : List α} {l' : List β}
    {i : Nat} {h : i < (zipWith f l l').length} :
    (zipWith f l l')[i] =
      f (l[i]'(lt_length_left_of_zipWith h))
        (l'[i]'(lt_length_right_of_zipWith h)) := by
  rw [← Option.some_inj, ← getElem?_eq_getElem, getElem?_zipWith_eq_some]
  exact
    ⟨l[i]'(lt_length_left_of_zipWith h), l'[i]'(lt_length_right_of_zipWith h),
      by rw [getElem?_eq_getElem], by rw [getElem?_eq_getElem]; exact ⟨rfl, rfl⟩⟩

theorem zipWith_eq_zipWith_take_min : ∀ (l₁ : List α) (l₂ : List β),
    zipWith f l₁ l₂ = zipWith f (l₁.take (min l₁.length l₂.length)) (l₂.take (min l₁.length l₂.length))
  | [], _ => by simp
  | _, [] => by simp
  | a :: l₁, b :: l₂ => by simp [succ_min_succ, zipWith_eq_zipWith_take_min l₁ l₂]

theorem reverse_zipWith (h : l.length = l'.length) :
    (zipWith f l l').reverse = zipWith f l.reverse l'.reverse := by
  induction l generalizing l' with
  | nil => simp
  | cons hd tl hl =>
    cases l' with
    | nil => simp
    | cons hd' tl' =>
      simp only [Nat.add_right_cancel_iff, length] at h
      have : tl.reverse.length = tl'.reverse.length := by simp [h]
      simp [hl h, zipWith_append _ _ _ _ _ this]

@[deprecated reverse_zipWith (since := "2024-07-28")] abbrev zipWith_distrib_reverse := @reverse_zipWith

@[simp] theorem zipWith_replicate {a : α} {b : β} {m n : Nat} :
    zipWith f (replicate m a) (replicate n b) = replicate (min m n) (f a b) := by
  rw [zipWith_eq_zipWith_take_min]
  simp

/-! ### zip -/

@[simp] theorem length_zip (l₁ : List α) (l₂ : List β) :
    length (zip l₁ l₂) = min (length l₁) (length l₂) := by
  simp [zip]

theorem lt_length_left_of_zip {i : Nat} {l : List α} {l' : List β} (h : i < (zip l l').length) :
    i < l.length :=
  lt_length_left_of_zipWith h

theorem lt_length_right_of_zip {i : Nat} {l : List α} {l' : List β} (h : i < (zip l l').length) :
    i < l'.length :=
  lt_length_right_of_zipWith h

@[simp]
theorem getElem_zip {l : List α} {l' : List β} {i : Nat} {h : i < (zip l l').length} :
    (zip l l')[i] =
      (l[i]'(lt_length_left_of_zip h), l'[i]'(lt_length_right_of_zip h)) :=
  getElem_zipWith (h := h)

theorem zip_eq_zip_take_min : ∀ (l₁ : List α) (l₂ : List β),
    zip l₁ l₂ = zip (l₁.take (min l₁.length l₂.length)) (l₂.take (min l₁.length l₂.length))
  | [], _ => by simp
  | _, [] => by simp
  | a :: l₁, b :: l₂ => by simp [succ_min_succ, zip_eq_zip_take_min l₁ l₂]

@[simp] theorem zip_replicate {a : α} {b : β} {m n : Nat} :
    zip (replicate m a) (replicate n b) = replicate (min m n) (a, b) := by
  rw [zip_eq_zip_take_min]
  simp

end List
