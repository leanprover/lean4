/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
prelude
import Init.Data.List.Lemmas
import Init.Data.Nat.Lemmas

/-!
# Lemmas about `List.take`, `List.drop`, `List.zip` and `List.zipWith`.

These are in a separate file from most of the list lemmas
as they required importing more lemmas about natural numbers.
-/

namespace List

open Nat

/-! ### take -/

abbrev take_succ_cons := @take_cons_succ

@[simp] theorem length_take : ∀ (i : Nat) (l : List α), length (take i l) = min i (length l)
  | 0, l => by simp [Nat.zero_min]
  | succ n, [] => by simp [Nat.min_zero]
  | succ n, _ :: l => by simp [Nat.succ_min_succ, length_take]

theorem length_take_le (n) (l : List α) : length (take n l) ≤ n := by simp [Nat.min_le_left]

theorem length_take_le' (n) (l : List α) : length (take n l) ≤ l.length :=
  by simp [Nat.min_le_right]

theorem length_take_of_le (h : n ≤ length l) : length (take n l) = n := by simp [Nat.min_eq_left h]

theorem take_all_of_le {n} {l : List α} (h : length l ≤ n) : take n l = l :=
  take_length_le h

@[simp]
theorem take_left : ∀ l₁ l₂ : List α, take (length l₁) (l₁ ++ l₂) = l₁
  | [], _ => rfl
  | a :: l₁, l₂ => congrArg (cons a) (take_left l₁ l₂)

theorem take_left' {l₁ l₂ : List α} {n} (h : length l₁ = n) : take n (l₁ ++ l₂) = l₁ := by
  rw [← h]; apply take_left

theorem take_take : ∀ (n m) (l : List α), take n (take m l) = take (min n m) l
  | n, 0, l => by rw [Nat.min_zero, take_zero, take_nil]
  | 0, m, l => by rw [Nat.zero_min, take_zero, take_zero]
  | succ n, succ m, nil => by simp only [take_nil]
  | succ n, succ m, a :: l => by
    simp only [take, succ_min_succ, take_take n m l]

theorem take_replicate (a : α) : ∀ n m : Nat, take n (replicate m a) = replicate (min n m) a
  | n, 0 => by simp [Nat.min_zero]
  | 0, m => by simp [Nat.zero_min]
  | succ n, succ m => by simp [succ_min_succ, take_replicate]

theorem map_take (f : α → β) :
    ∀ (L : List α) (i : Nat), (L.take i).map f = (L.map f).take i
  | [], i => by simp
  | _, 0 => by simp
  | h :: t, n + 1 => by dsimp; rw [map_take f t n]

/-- Taking the first `n` elements in `l₁ ++ l₂` is the same as appending the first `n` elements
of `l₁` to the first `n - l₁.length` elements of `l₂`. -/
theorem take_append_eq_append_take {l₁ l₂ : List α} {n : Nat} :
    take n (l₁ ++ l₂) = take n l₁ ++ take (n - l₁.length) l₂ := by
  induction l₁ generalizing n
  · simp
  · cases n
    · simp [*]
    · simp only [cons_append, take_cons_succ, length_cons, succ_eq_add_one, cons.injEq,
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
  rw [take_append_eq_append_take, take_all_of_le (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

/-- The `i`-th element of a list coincides with the `i`-th element of any of its prefixes of
length `> i`. Version designed to rewrite from the big list to the small list. -/
theorem getElem_take (L : List α) {i j : Nat} (hi : i < L.length) (hj : i < j) :
    L[i] = (L.take j)[i]'(length_take .. ▸ Nat.lt_min.mpr ⟨hj, hi⟩) :=
  getElem_of_eq (take_append_drop j L).symm _ ▸ getElem_append ..

/-- The `i`-th element of a list coincides with the `i`-th element of any of its prefixes of
length `> i`. Version designed to rewrite from the small list to the big list. -/
theorem getElem_take' (L : List α) {j i : Nat} {h : i < (L.take j).length} :
    (L.take j)[i] =
    L[i]'(Nat.lt_of_lt_of_le h (length_take_le' _ _)) := by
  rw [length_take, Nat.lt_min] at h; rw [getElem_take L _ h.1]

/-- The `i`-th element of a list coincides with the `i`-th element of any of its prefixes of
length `> i`. Version designed to rewrite from the big list to the small list. -/
@[deprecated getElem_take (since := "2024-06-12")]
theorem get_take (L : List α) {i j : Nat} (hi : i < L.length) (hj : i < j) :
    get L ⟨i, hi⟩ = get (L.take j) ⟨i, length_take .. ▸ Nat.lt_min.mpr ⟨hj, hi⟩⟩ := by
  simp [getElem_take _ hi hj]

/-- The `i`-th element of a list coincides with the `i`-th element of any of its prefixes of
length `> i`. Version designed to rewrite from the small list to the big list. -/
@[deprecated getElem_take (since := "2024-06-12")]
theorem get_take' (L : List α) {j i} :
    get (L.take j) i =
    get L ⟨i.1, Nat.lt_of_lt_of_le i.2 (length_take_le' _ _)⟩ := by
  simp [getElem_take']

theorem getElem?_take {l : List α} {n m : Nat} (h : m < n) : (l.take n)[m]? = l[m]? := by
  induction n generalizing l m with
  | zero =>
    exact absurd h (Nat.not_lt_of_le m.zero_le)
  | succ _ hn =>
    cases l with
    | nil => simp only [take_nil]
    | cons hd tl =>
      cases m
      · simp
      · simpa using hn (Nat.lt_of_succ_lt_succ h)

@[deprecated getElem?_take (since := "2024-06-12")]
theorem get?_take {l : List α} {n m : Nat} (h : m < n) : (l.take n).get? m = l.get? m := by
  simp [getElem?_take, h]

theorem getElem?_take_eq_none {l : List α} {n m : Nat} (h : n ≤ m) :
    (l.take n)[m]? = none :=
  getElem?_eq_none.mpr <| Nat.le_trans (length_take_le _ _) h

@[deprecated getElem?_take_eq_none (since := "2024-06-12")]
theorem get?_take_eq_none {l : List α} {n m : Nat} (h : n ≤ m) :
    (l.take n).get? m = none := by
  simp [getElem?_take_eq_none h]

theorem getElem?_take_eq_if {l : List α} {n m : Nat} :
    (l.take n)[m]? = if m < n then l[m]? else none := by
  split
  · next h => exact getElem?_take h
  · next h => exact getElem?_take_eq_none (Nat.le_of_not_lt h)

@[deprecated getElem?_take_eq_if (since := "2024-06-12")]
theorem get?_take_eq_if {l : List α} {n m : Nat} :
    (l.take n).get? m = if m < n then l.get? m else none := by
  simp [getElem?_take_eq_if]

@[simp]
theorem get?_take_of_succ {l : List α} {n : Nat} : (l.take (n + 1))[n]? = l[n]? :=
  getElem?_take (Nat.lt_succ_self n)

theorem take_succ {l : List α} {n : Nat} : l.take (n + 1) = l.take n ++ l[n]?.toList := by
  induction l generalizing n with
  | nil =>
    simp only [take_nil, Option.toList, getElem?_nil, append_nil]
  | cons hd tl hl =>
    cases n
    · simp only [take, Option.toList, getElem?_cons_zero, nil_append]
    · simp only [take, hl, getElem?_cons_succ, cons_append]

@[simp]
theorem take_eq_nil_iff {l : List α} {k : Nat} : l.take k = [] ↔ l = [] ∨ k = 0 := by
  cases l <;> cases k <;> simp [Nat.succ_ne_zero]

@[simp]
theorem take_eq_take :
    ∀ {l : List α} {m n : Nat}, l.take m = l.take n ↔ min m l.length = min n l.length
  | [], m, n => by simp [Nat.min_zero]
  | _ :: xs, 0, 0 => by simp
  | x :: xs, m + 1, 0 => by simp [Nat.zero_min, succ_min_succ]
  | x :: xs, 0, n + 1 => by simp [Nat.zero_min, succ_min_succ]
  | x :: xs, m + 1, n + 1 => by simp [succ_min_succ, take_eq_take]; omega

theorem take_add (l : List α) (m n : Nat) : l.take (m + n) = l.take m ++ (l.drop m).take n := by
  suffices take (m + n) (take m l ++ drop m l) = take m l ++ take n (drop m l) by
    rw [take_append_drop] at this
    assumption
  rw [take_append_eq_append_take, take_all_of_le, append_right_inj]
  · simp only [take_eq_take, length_take, length_drop]
    omega
  apply Nat.le_trans (m := m)
  · apply length_take_le
  · apply Nat.le_add_right

theorem take_eq_nil_of_eq_nil : ∀ {as : List α} {i}, as = [] → as.take i = []
  | _, _, rfl => take_nil

theorem ne_nil_of_take_ne_nil {as : List α} {i : Nat} (h: as.take i ≠ []) : as ≠ [] :=
  mt take_eq_nil_of_eq_nil h

theorem dropLast_eq_take (l : List α) : l.dropLast = l.take l.length.pred := by
  cases l with
  | nil => simp [dropLast]
  | cons x l =>
    induction l generalizing x with
    | nil => simp [dropLast]
    | cons hd tl hl => simp [dropLast, hl]

theorem dropLast_take {n : Nat} {l : List α} (h : n < l.length) :
    (l.take n).dropLast = l.take n.pred := by
  simp only [dropLast_eq_take, length_take, Nat.le_of_lt h, take_take, pred_le, Nat.min_eq_left]

theorem map_eq_append_split {f : α → β} {l : List α} {s₁ s₂ : List β}
    (h : map f l = s₁ ++ s₂) : ∃ l₁ l₂, l = l₁ ++ l₂ ∧ map f l₁ = s₁ ∧ map f l₂ = s₂ := by
  have := h
  rw [← take_append_drop (length s₁) l] at this ⊢
  rw [map_append] at this
  refine ⟨_, _, rfl, append_inj this ?_⟩
  rw [length_map, length_take, Nat.min_eq_left]
  rw [← length_map l f, h, length_append]
  apply Nat.le_add_right

/-! ### drop -/

@[simp]
theorem drop_eq_nil_iff_le {l : List α} {k : Nat} : l.drop k = [] ↔ l.length ≤ k := by
  refine' ⟨fun h => _, drop_eq_nil_of_le⟩
  induction k generalizing l with
  | zero =>
    simp only [drop] at h
    simp [h]
  | succ k hk =>
    cases l
    · simp
    · simp only [drop] at h
      simpa [Nat.succ_le_succ_iff] using hk h

theorem drop_length_cons {l : List α} (h : l ≠ []) (a : α) :
    (a :: l).drop l.length = [l.getLast h] := by
  induction l generalizing a with
  | nil =>
    cases h rfl
  | cons y l ih =>
    simp only [drop, length]
    by_cases h₁ : l = []
    · simp [h₁]
    rw [getLast_cons' _ h₁]
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

theorem drop_sizeOf_le [SizeOf α] (l : List α) (n : Nat) : sizeOf (l.drop n) ≤ sizeOf l := by
  induction l generalizing n with
  | nil => rw [drop_nil]; apply Nat.le_refl
  | cons _ _ lih =>
    induction n with
    | zero => apply Nat.le_refl
    | succ n =>
      exact Trans.trans (lih _) (Nat.le_add_left _ _)

theorem lt_length_drop (L : List α) {i j : Nat} (h : i + j < L.length) : j < (L.drop i).length := by
  have A : i < L.length := Nat.lt_of_le_of_lt (Nat.le.intro rfl) h
  rw [(take_append_drop i L).symm] at h
  simpa only [Nat.le_of_lt A, Nat.min_eq_left, Nat.add_lt_add_iff_left, length_take,
    length_append] using h

/-- The `i + j`-th element of a list coincides with the `j`-th element of the list obtained by
dropping the first `i` elements. Version designed to rewrite from the big list to the small list. -/
theorem getElem_drop (L : List α) {i j : Nat} (h : i + j < L.length) :
    L[i + j] = (L.drop i)[j]'(lt_length_drop L h) := by
  have : i ≤ L.length := Nat.le_trans (Nat.le_add_right _ _) (Nat.le_of_lt h)
  rw [getElem_of_eq (take_append_drop i L).symm h, getElem_append_right'] <;>
    simp [Nat.min_eq_left this, Nat.add_sub_cancel_left, Nat.le_add_right]

/-- The `i + j`-th element of a list coincides with the `j`-th element of the list obtained by
dropping the first `i` elements. Version designed to rewrite from the big list to the small list. -/
@[deprecated getElem_drop (since := "2024-06-12")]
theorem get_drop (L : List α) {i j : Nat} (h : i + j < L.length) :
    get L ⟨i + j, h⟩ = get (L.drop i) ⟨j, lt_length_drop L h⟩ := by
  simp [getElem_drop]

/-- The `i + j`-th element of a list coincides with the `j`-th element of the list obtained by
dropping the first `i` elements. Version designed to rewrite from the small list to the big list. -/
theorem getElem_drop' (L : List α) {i : Nat} {j : Nat} {h : j < (L.drop i).length} :
    (L.drop i)[j] = L[i + j]'(by
      rw [Nat.add_comm]
      exact Nat.add_lt_of_lt_sub (length_drop i L ▸ h)) := by
  rw [getElem_drop]

/-- The `i + j`-th element of a list coincides with the `j`-th element of the list obtained by
dropping the first `i` elements. Version designed to rewrite from the small list to the big list. -/
@[deprecated getElem_drop' (since := "2024-06-12")]
theorem get_drop' (L : List α) {i j} :
    get (L.drop i) j = get L ⟨i + j, by
      rw [Nat.add_comm]
      exact Nat.add_lt_of_lt_sub (length_drop i L ▸ j.2)⟩ := by
  simp [getElem_drop']

@[simp]
theorem getElem?_drop (L : List α) (i j : Nat) : (L.drop i)[j]? = L[i + j]? := by
  ext
  simp only [getElem?_eq_some, getElem_drop', Option.mem_def]
  constructor <;> intro ⟨h, ha⟩
  · exact ⟨_, ha⟩
  · refine ⟨?_, ha⟩
    rw [length_drop]
    rw [Nat.add_comm] at h
    apply Nat.lt_sub_of_add_lt h

@[deprecated getElem?_drop (since := "2024-06-12")]
theorem get?_drop (L : List α) (i j : Nat) : get? (L.drop i) j = get? L (i + j) := by
  simp

@[simp] theorem drop_drop (n : Nat) : ∀ (m) (l : List α), drop n (drop m l) = drop (n + m) l
  | m, [] => by simp
  | 0, l => by simp
  | m + 1, a :: l =>
    calc
      drop n (drop (m + 1) (a :: l)) = drop n (drop m l) := rfl
      _ = drop (n + m) l := drop_drop n m l
      _ = drop (n + (m + 1)) (a :: l) := rfl

theorem take_drop : ∀ (m n : Nat) (l : List α), take n (drop m l) = drop m (take (m + n) l)
  | 0, _, _ => by simp
  | _, _, [] => by simp
  | _+1, _, _ :: _ => by simpa [Nat.succ_add, take_succ_cons, drop_succ_cons] using take_drop ..

theorem drop_take : ∀ (m n : Nat) (l : List α), drop n (take m l) = take (m - n) (drop n l)
  | 0, _, _ => by simp
  | _, 0, _ => by simp
  | _, _, [] => by simp
  | m+1, n+1, h :: t => by
    simp [take_succ_cons, drop_succ_cons, drop_take m n t]
    congr 1
    omega

theorem map_drop (f : α → β) :
    ∀ (L : List α) (i : Nat), (L.drop i).map f = (L.map f).drop i
  | [], i => by simp
  | L, 0 => by simp
  | h :: t, n + 1 => by
    dsimp
    rw [map_drop f t]

theorem reverse_take {α} {xs : List α} (n : Nat) (h : n ≤ xs.length) :
    xs.reverse.take n = (xs.drop (xs.length - n)).reverse := by
  induction xs generalizing n <;>
    simp only [reverse_cons, drop, reverse_nil, Nat.zero_sub, length, take_nil]
  next xs_hd xs_tl xs_ih =>
  cases Nat.lt_or_eq_of_le h with
  | inl h' =>
    have h' := Nat.le_of_succ_le_succ h'
    rw [take_append_of_le_length, xs_ih _ h']
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

@[simp]
theorem getElem_cons_drop : ∀ (l : List α) (i : Nat) (h : i < l.length),
    l[i] :: drop (i + 1) l = drop i l
  | _::_, 0, _ => rfl
  | _::_, i+1, _ => getElem_cons_drop _ i _

@[deprecated getElem_cons_drop (since := "2024-06-12")]
theorem get_cons_drop (l : List α) (i) : get l i :: drop (i + 1) l = drop i l := by
  simp

theorem drop_eq_getElem_cons {n} {l : List α} (h) : drop n l = l[n] :: drop (n + 1) l :=
  (getElem_cons_drop _ n h).symm

@[deprecated drop_eq_getElem_cons (since := "2024-06-12")]
theorem drop_eq_get_cons {n} {l : List α} (h) : drop n l = get l ⟨n, h⟩ :: drop (n + 1) l := by
  simp [drop_eq_getElem_cons]

theorem drop_eq_nil_of_eq_nil : ∀ {as : List α} {i}, as = [] → as.drop i = []
  | _, _, rfl => drop_nil

theorem ne_nil_of_drop_ne_nil {as : List α} {i : Nat} (h: as.drop i ≠ []) : as ≠ [] :=
  mt drop_eq_nil_of_eq_nil h

/-! ### zipWith -/

@[simp] theorem length_zipWith (f : α → β → γ) (l₁ l₂) :
    length (zipWith f l₁ l₂) = min (length l₁) (length l₂) := by
  induction l₁ generalizing l₂ <;> cases l₂ <;>
    simp_all [succ_min_succ, Nat.zero_min, Nat.min_zero]

/-! ### zip -/

@[simp] theorem length_zip (l₁ : List α) (l₂ : List β) :
    length (zip l₁ l₂) = min (length l₁) (length l₂) := by
  simp [zip]

end List
