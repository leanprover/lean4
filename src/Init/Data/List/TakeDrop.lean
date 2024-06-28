/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
prelude
import Init.Data.List.Lemmas
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

theorem take_take : ∀ (n m) (l : List α), take n (take m l) = take (min n m) l
  | n, 0, l => by rw [Nat.min_zero, take_zero, take_nil]
  | 0, m, l => by rw [Nat.zero_min, take_zero, take_zero]
  | succ n, succ m, nil => by simp only [take_nil]
  | succ n, succ m, a :: l => by
    simp only [take, succ_min_succ, take_take n m l]

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

theorem getElem?_take_eq_none {l : List α} {n m : Nat} (h : n ≤ m) :
    (l.take n)[m]? = none :=
  getElem?_eq_none <| Nat.le_trans (length_take_le _ _) h

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

theorem set_eq_take_append_cons_drop {l : List α} {n : Nat} {a : α} :
    l.set n a = if n < l.length then l.take n ++ a :: l.drop (n + 1) else l := by
  split <;> rename_i h
  · ext1 m
    by_cases h' : m < n
    · rw [getElem?_append (by simp [length_take]; omega), getElem?_set_ne (by omega),
        getElem?_take h']
    · by_cases h'' : m = n
      · subst h''
        rw [getElem?_set_eq (by simp; omega), getElem?_append_right, length_take,
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

theorem drop_take : ∀ (m n : Nat) (l : List α), drop n (take m l) = take (m - n) (drop n l)
  | 0, _, _ => by simp
  | _, 0, _ => by simp
  | _, _, [] => by simp
  | m+1, n+1, h :: t => by
    simp [take_succ_cons, drop_succ_cons, drop_take m n t]
    congr 1
    omega

theorem take_reverse {α} {xs : List α} (n : Nat) (h : n ≤ xs.length) :
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

@[deprecated (since := "2024-06-15")] abbrev reverse_take := @take_reverse

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

theorem zipWith_eq_zipWith_take_min : ∀ (l₁ : List α) (l₂ : List β),
    zipWith f l₁ l₂ = zipWith f (l₁.take (min l₁.length l₂.length)) (l₂.take (min l₁.length l₂.length))
  | [], _ => by simp
  | _, [] => by simp
  | a :: l₁, b :: l₂ => by simp [succ_min_succ, zipWith_eq_zipWith_take_min l₁ l₂]

@[simp] theorem zipWith_replicate {a : α} {b : β} {m n : Nat} :
    zipWith f (replicate m a) (replicate n b) = replicate (min m n) (f a b) := by
  rw [zipWith_eq_zipWith_take_min]
  simp

/-! ### zip -/

@[simp] theorem length_zip (l₁ : List α) (l₂ : List β) :
    length (zip l₁ l₂) = min (length l₁) (length l₂) := by
  simp [zip]

theorem zip_eq_zip_take_min : ∀ (l₁ : List α) (l₂ : List β),
    zip l₁ l₂ = zip (l₁.take (min l₁.length l₂.length)) (l₂.take (min l₁.length l₂.length))
  | [], _ => by simp
  | _, [] => by simp
  | a :: l₁, b :: l₂ => by simp [succ_min_succ, zip_eq_zip_take_min l₁ l₂]

@[simp] theorem zip_replicate {a : α} {b : β} {m n : Nat} :
    zip (replicate m a) (replicate n b) = replicate (min m n) (a, b) := by
  rw [zip_eq_zip_take_min]
  simp

/-! ### minimum? -/

-- A specialization of `minimum?_eq_some_iff` to Nat.
theorem minimum?_eq_some_iff' {xs : List Nat} :
    xs.minimum? = some a ↔ (a ∈ xs ∧ ∀ b ∈ xs, a ≤ b) :=
  minimum?_eq_some_iff
    (le_refl := Nat.le_refl)
    (min_eq_or := fun _ _ => by omega)
    (le_min_iff := fun _ _ _ => by omega)

/-! ### maximum? -/

-- A specialization of `maximum?_eq_some_iff` to Nat.
theorem maximum?_eq_some_iff' {xs : List Nat} :
    xs.maximum? = some a ↔ (a ∈ xs ∧ ∀ b ∈ xs, b ≤ a) :=
  maximum?_eq_some_iff
    (le_refl := Nat.le_refl)
    (max_eq_or := fun _ _ => by omega)
    (max_le_iff := fun _ _ _ => by omega)

end List
