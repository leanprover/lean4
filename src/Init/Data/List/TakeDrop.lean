/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
prelude
import Init.Data.List.Lemmas

/-!
# Lemmas about `List.take` and `List.drop`.
-/

-- set_option linter.listName true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
-- set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace List

open Nat

/-! ### take and drop

Further results on `List.take` and `List.drop`, which rely on stronger automation in `Nat`,
are given in `Init.Data.List.TakeDrop`.
-/

theorem take_cons {l : List α} (h : 0 < i) : take i (a :: l) = a :: take (i - 1) l := by
  cases i with
  | zero => exact absurd h (Nat.lt_irrefl _)
  | succ i => rfl

@[simp]
theorem drop_one : ∀ l : List α, drop 1 l = tail l
  | [] | _ :: _ => rfl

@[simp] theorem take_append_drop : ∀ (i : Nat) (l : List α), take i l ++ drop i l = l
  | 0, _ => rfl
  | _+1, [] => rfl
  | i+1, x :: xs => congrArg (cons x) <| take_append_drop i xs

@[simp] theorem length_drop : ∀ (i : Nat) (l : List α), length (drop i l) = length l - i
  | 0, _ => rfl
  | succ i, [] => Eq.symm (Nat.zero_sub (succ i))
  | succ i, x :: l => calc
    length (drop (succ i) (x :: l)) = length l - i := length_drop i l
    _ = succ (length l) - succ i := (Nat.succ_sub_succ_eq_sub (length l) i).symm

theorem drop_of_length_le {l : List α} (h : l.length ≤ i) : drop i l = [] :=
  length_eq_zero.1 (length_drop .. ▸ Nat.sub_eq_zero_of_le h)

theorem length_lt_of_drop_ne_nil {l : List α} {i} (h : drop i l ≠ []) : i < l.length :=
  gt_of_not_le (mt drop_of_length_le h)

theorem take_of_length_le {l : List α} (h : l.length ≤ i) : take i l = l := by
  have := take_append_drop i l
  rw [drop_of_length_le h, append_nil] at this; exact this

theorem lt_length_of_take_ne_self {l : List α} {i} (h : l.take i ≠ l) : i < l.length :=
  gt_of_not_le (mt take_of_length_le h)

@[deprecated drop_of_length_le (since := "2024-07-07")] abbrev drop_length_le := @drop_of_length_le
@[deprecated take_of_length_le (since := "2024-07-07")] abbrev take_length_le := @take_of_length_le

@[simp] theorem drop_length (l : List α) : drop l.length l = [] := drop_of_length_le (Nat.le_refl _)

@[simp] theorem take_length (l : List α) : take l.length l = l := take_of_length_le (Nat.le_refl _)

@[simp]
theorem getElem_cons_drop : ∀ (l : List α) (i : Nat) (h : i < l.length),
    l[i] :: drop (i + 1) l = drop i l
  | _::_, 0, _ => rfl
  | _::_, i+1, h => getElem_cons_drop _ i (Nat.add_one_lt_add_one_iff.mp h)

theorem drop_eq_getElem_cons {i} {l : List α} (h : i < l.length) : drop i l = l[i] :: drop (i + 1) l :=
  (getElem_cons_drop _ i h).symm

@[simp]
theorem getElem?_take_of_lt {l : List α} {i j : Nat} (h : i < j) : (l.take j)[i]? = l[i]? := by
  induction j generalizing l i with
  | zero =>
    exact absurd h (Nat.not_lt_of_le i.zero_le)
  | succ _ hj =>
    cases l with
    | nil => simp only [take_nil]
    | cons hd tl =>
      cases i
      · simp
      · simpa using hj (Nat.lt_of_succ_lt_succ h)

theorem getElem?_take_of_succ {l : List α} {i : Nat} : (l.take (i + 1))[i]? = l[i]? := by simp

@[simp] theorem drop_drop (i : Nat) : ∀ (j) (l : List α), drop i (drop j l) = drop (j + i) l
  | j, [] => by simp
  | 0, l => by simp
  | j + 1, a :: l =>
    calc
      drop i (drop (j + 1) (a :: l)) = drop i (drop j l) := rfl
      _ = drop (j + i) l := drop_drop i j l
      _ = drop ((j + 1) + i) (a :: l) := by rw [Nat.add_right_comm]; rfl

theorem drop_add_one_eq_tail_drop (l : List α) : l.drop (i + 1) = (l.drop i).tail := by
  rw [← drop_drop, drop_one]

theorem take_drop : ∀ (i j : Nat) (l : List α), take i (drop j l) = drop j (take (j + i) l)
  | _, 0, _ => by simp
  | _, _, [] => by simp
  | _, _+1, _ :: _ => by simpa [Nat.succ_add, take_succ_cons, drop_succ_cons] using take_drop ..

@[simp]
theorem tail_drop (l : List α) (i : Nat) : (l.drop i).tail = l.drop (i + 1) := by
  induction l generalizing i with
  | nil => simp
  | cons hd tl hl =>
    cases i
    · simp
    · simp [hl]

@[simp]
theorem drop_tail (l : List α) (i : Nat) : l.tail.drop i = l.drop (i + 1) := by
  rw [Nat.add_comm, ← drop_drop, drop_one]

@[simp]
theorem drop_eq_nil_iff {l : List α} {i : Nat} : l.drop i = [] ↔ l.length ≤ i := by
  refine ⟨fun h => ?_, drop_eq_nil_of_le⟩
  induction i generalizing l with
  | zero =>
    simp only [drop] at h
    simp [h]
  | succ i hi =>
    cases l
    · simp
    · simp only [drop] at h
      simpa [Nat.succ_le_succ_iff] using hi h

@[deprecated drop_eq_nil_iff (since := "2024-09-10")] abbrev drop_eq_nil_iff_le := @drop_eq_nil_iff

@[simp]
theorem take_eq_nil_iff {l : List α} {k : Nat} : l.take k = [] ↔ k = 0 ∨ l = [] := by
  cases l <;> cases k <;> simp [Nat.succ_ne_zero]

theorem drop_eq_nil_of_eq_nil : ∀ {as : List α} {i}, as = [] → as.drop i = []
  | _, _, rfl => drop_nil

theorem ne_nil_of_drop_ne_nil {as : List α} {i : Nat} (h: as.drop i ≠ []) : as ≠ [] :=
  mt drop_eq_nil_of_eq_nil h

theorem take_eq_nil_of_eq_nil : ∀ {as : List α} {i}, as = [] → as.take i = []
  | _, _, rfl => take_nil

theorem ne_nil_of_take_ne_nil {as : List α} {i : Nat} (h : as.take i ≠ []) : as ≠ [] :=
  mt take_eq_nil_of_eq_nil h

theorem set_take {l : List α} {i j : Nat} {a : α} :
    (l.set j a).take i = (l.take i).set j a := by
  induction i generalizing l j with
  | zero => simp
  | succ _ hi =>
    cases l with
    | nil => simp
    | cons hd tl => cases j <;> simp_all

theorem drop_set {l : List α} {i j : Nat} {a : α} :
    (l.set j a).drop i = if j < i then l.drop i else (l.drop i).set (j - i) a := by
  induction i generalizing l j with
  | zero => simp
  | succ _ hi =>
    cases l with
    | nil => simp
    | cons hd tl =>
      cases j
      · simp_all
      · simp only [hi, set_cons_succ, drop_succ_cons, succ_lt_succ_iff]
        congr 2
        exact (Nat.add_sub_add_right ..).symm

theorem set_drop {l : List α} {i j : Nat} {a : α} :
    (l.drop i).set j a = (l.set (i + j) a).drop i := by
  rw [drop_set, if_neg, add_sub_self_left]
  exact (Nat.not_lt).2 (le_add_right ..)

theorem take_concat_get (l : List α) (i : Nat) (h : i < l.length) :
    (l.take i).concat l[i] = l.take (i+1) :=
  Eq.symm <| (append_left_inj _).1 <| (take_append_drop (i+1) l).trans <| by
    rw [concat_eq_append, append_assoc, singleton_append, getElem_cons_drop_succ_eq_drop, take_append_drop]

@[simp] theorem take_append_getElem (l : List α) (i : Nat) (h : i < l.length) :
    (l.take i) ++ [l[i]] = l.take (i+1) := by
  simpa using take_concat_get l i h

theorem take_succ_eq_append_getElem {i} {l : List α} (h : i < l.length) : l.take (i + 1) = l.take i ++ [l[i]] :=
  (take_append_getElem _ _ h).symm

@[simp] theorem take_append_getLast (l : List α) (h : l ≠ []) :
    (l.take (l.length - 1)) ++ [l.getLast h] = l := by
  rw [getLast_eq_getElem]
  cases l
  · contradiction
  · simp

@[simp] theorem take_append_getLast? (l : List α) :
    (l.take (l.length - 1)) ++ l.getLast?.toList = l := by
  match l with
  | [] => simp
  | x :: xs =>
    simpa using take_append_getLast (x :: xs) (by simp)

@[deprecated take_succ_cons (since := "2024-07-25")]
theorem take_cons_succ : (a::as).take (i+1) = a :: as.take i := rfl

@[deprecated take_of_length_le (since := "2024-07-25")]
theorem take_all_of_le {l : List α} {i} (h : length l ≤ i) : take i l = l :=
  take_of_length_le h

theorem drop_left : ∀ l₁ l₂ : List α, drop (length l₁) (l₁ ++ l₂) = l₂
  | [], _ => rfl
  | _ :: l₁, l₂ => drop_left l₁ l₂

@[simp]
theorem drop_left' {l₁ l₂ : List α} {i} (h : length l₁ = i) : drop i (l₁ ++ l₂) = l₂ := by
  rw [← h]; apply drop_left

theorem take_left : ∀ l₁ l₂ : List α, take (length l₁) (l₁ ++ l₂) = l₁
  | [], _ => rfl
  | a :: l₁, l₂ => congrArg (cons a) (take_left l₁ l₂)

@[simp]
theorem take_left' {l₁ l₂ : List α} {i} (h : length l₁ = i) : take i (l₁ ++ l₂) = l₁ := by
  rw [← h]; apply take_left

theorem take_succ {l : List α} {i : Nat} : l.take (i + 1) = l.take i ++ l[i]?.toList := by
  induction l generalizing i with
  | nil =>
    simp only [take_nil, Option.toList, getElem?_nil, append_nil]
  | cons hd tl hl =>
    cases i
    · simp only [take, Option.toList, getElem?_cons_zero, nil_append]
    · simp only [take, hl, getElem?_cons_succ, cons_append]

@[deprecated "Deprecated without replacement." (since := "2024-07-25")]
theorem drop_sizeOf_le [SizeOf α] (l : List α) (i : Nat) : sizeOf (l.drop i) ≤ sizeOf l := by
  induction l generalizing i with
  | nil => rw [drop_nil]; apply Nat.le_refl
  | cons _ _ lih =>
    induction i with
    | zero => apply Nat.le_refl
    | succ n =>
      exact Trans.trans (lih _) (Nat.le_add_left _ _)

theorem dropLast_eq_take (l : List α) : l.dropLast = l.take (l.length - 1) := by
  cases l with
  | nil => simp [dropLast]
  | cons x l =>
    induction l generalizing x <;> simp_all [dropLast]

@[simp] theorem map_take (f : α → β) :
    ∀ (l : List α) (i : Nat), (l.take i).map f = (l.map f).take i
  | [], i => by simp
  | _, 0 => by simp
  | _ :: tl, n + 1 => by dsimp; rw [map_take f tl n]

@[simp] theorem map_drop (f : α → β) :
    ∀ (l : List α) (i : Nat), (l.drop i).map f = (l.map f).drop i
  | [], i => by simp
  | l, 0 => by simp
  | _ :: tl, n + 1 => by
    dsimp
    rw [map_drop f tl]

/-! ### takeWhile and dropWhile -/

theorem takeWhile_cons (p : α → Bool) (a : α) (l : List α) :
    (a :: l).takeWhile p = if p a then a :: l.takeWhile p else [] := by
  simp only [takeWhile]
  by_cases h: p a <;> simp [h]

@[simp] theorem takeWhile_cons_of_pos {p : α → Bool} {a : α} {l : List α} (h : p a) :
    (a :: l).takeWhile p = a :: l.takeWhile p := by
  simp [takeWhile_cons, h]

@[simp] theorem takeWhile_cons_of_neg {p : α → Bool} {a : α} {l : List α} (h : ¬ p a) :
    (a :: l).takeWhile p = [] := by
  simp [takeWhile_cons, h]

theorem dropWhile_cons :
    (x :: xs : List α).dropWhile p = if p x then xs.dropWhile p else x :: xs := by
  split <;> simp_all [dropWhile]

@[simp] theorem dropWhile_cons_of_pos {a : α} {l : List α} (h : p a) :
    (a :: l).dropWhile p = l.dropWhile p := by
  simp [dropWhile_cons, h]

@[simp] theorem dropWhile_cons_of_neg {a : α} {l : List α} (h : ¬ p a) :
    (a :: l).dropWhile p = a :: l := by
  simp [dropWhile_cons, h]

theorem head?_takeWhile (p : α → Bool) (l : List α) : (l.takeWhile p).head? = l.head?.filter p := by
  cases l with
  | nil => rfl
  | cons x xs =>
    simp only [takeWhile_cons, head?_cons, Option.filter_some]
    split <;> simp

theorem head_takeWhile (p : α → Bool) (l : List α) (w) :
    (l.takeWhile p).head w = l.head (by rintro rfl; simp_all) := by
  cases l with
  | nil => rfl
  | cons x xs =>
    simp only [takeWhile_cons, head_cons]
    simp only [takeWhile_cons] at w
    split <;> simp_all

theorem head?_dropWhile_not (p : α → Bool) (l : List α) :
    match (l.dropWhile p).head? with | some x => p x = false | none => True := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [dropWhile_cons]
    split <;> rename_i h <;> split at h <;> simp_all

theorem head_dropWhile_not (p : α → Bool) (l : List α) (w) :
    p ((l.dropWhile p).head w) = false := by
  simpa [head?_eq_head, w] using head?_dropWhile_not p l

theorem takeWhile_map (f : α → β) (p : β → Bool) (l : List α) :
    (l.map f).takeWhile p = (l.takeWhile (p ∘ f)).map f := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [map_cons, takeWhile_cons]
    split <;> simp_all

theorem dropWhile_map (f : α → β) (p : β → Bool) (l : List α) :
    (l.map f).dropWhile p = (l.dropWhile (p ∘ f)).map f := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [map_cons, dropWhile_cons]
    split <;> simp_all

theorem takeWhile_filterMap (f : α → Option β) (p : β → Bool) (l : List α) :
    (l.filterMap f).takeWhile p = (l.takeWhile fun a => (f a).all p).filterMap f := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [filterMap_cons]
    split <;> rename_i h
    · simp only [takeWhile_cons, h]
      split <;> simp_all
    · simp [takeWhile_cons, h, ih]
      split <;> simp_all [filterMap_cons]

theorem dropWhile_filterMap (f : α → Option β) (p : β → Bool) (l : List α) :
    (l.filterMap f).dropWhile p = (l.dropWhile fun a => (f a).all p).filterMap f := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [filterMap_cons]
    split <;> rename_i h
    · simp only [dropWhile_cons, h]
      split <;> simp_all
    · simp [dropWhile_cons, h, ih]
      split <;> simp_all [filterMap_cons]

theorem takeWhile_filter (p q : α → Bool) (l : List α) :
    (l.filter p).takeWhile q = (l.takeWhile fun a => !p a || q a).filter p := by
  simp [← filterMap_eq_filter, takeWhile_filterMap]

theorem dropWhile_filter (p q : α → Bool) (l : List α) :
    (l.filter p).dropWhile q = (l.dropWhile fun a => !p a || q a).filter p := by
  simp [← filterMap_eq_filter, dropWhile_filterMap]

@[simp] theorem takeWhile_append_dropWhile (p : α → Bool) :
    ∀ (l : List α), takeWhile p l ++ dropWhile p l = l
  | [] => rfl
  | x :: xs => by simp [takeWhile, dropWhile]; cases p x <;> simp [takeWhile_append_dropWhile p xs]

theorem takeWhile_append {xs ys : List α} :
    (xs ++ ys).takeWhile p =
      if (xs.takeWhile p).length = xs.length then xs ++ ys.takeWhile p else xs.takeWhile p := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [cons_append, takeWhile_cons]
    split
    · simp_all only [length_cons, add_one_inj]
      split <;> rfl
    · simp_all

@[simp] theorem takeWhile_append_of_pos {p : α → Bool} {l₁ l₂ : List α} (h : ∀ a ∈ l₁, p a) :
    (l₁ ++ l₂).takeWhile p = l₁ ++ l₂.takeWhile p := by
  induction l₁ with
  | nil => simp
  | cons x xs ih => simp_all [takeWhile_cons]

theorem dropWhile_append {xs ys : List α} :
    (xs ++ ys).dropWhile p =
      if (xs.dropWhile p).isEmpty then ys.dropWhile p else xs.dropWhile p ++ ys := by
  induction xs with
  | nil => simp
  | cons _ _ ih =>
    simp only [cons_append, dropWhile_cons]
    split <;> simp_all

@[simp] theorem dropWhile_append_of_pos {p : α → Bool} {l₁ l₂ : List α} (h : ∀ a ∈ l₁, p a) :
    (l₁ ++ l₂).dropWhile p = l₂.dropWhile p := by
  induction l₁ with
  | nil => simp
  | cons x xs ih => simp_all [dropWhile_cons]

@[simp] theorem takeWhile_replicate_eq_filter (p : α → Bool) :
    (replicate n a).takeWhile p = (replicate n a).filter p := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [replicate_succ, takeWhile_cons]
    split <;> simp_all

theorem takeWhile_replicate (p : α → Bool) :
    (replicate n a).takeWhile p = if p a then replicate n a else [] := by
  rw [takeWhile_replicate_eq_filter, filter_replicate]

@[simp] theorem dropWhile_replicate_eq_filter_not (p : α → Bool) :
    (replicate n a).dropWhile p = (replicate n a).filter (fun a => !p a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [replicate_succ, dropWhile_cons]
    split <;> simp_all

theorem dropWhile_replicate (p : α → Bool) :
    (replicate n a).dropWhile p = if p a then [] else replicate n a := by
  simp only [dropWhile_replicate_eq_filter_not, filter_replicate]
  split <;> simp_all

theorem take_takeWhile {l : List α} (p : α → Bool) i :
    (l.takeWhile p).take i = (l.take i).takeWhile p := by
  induction l generalizing i with
  | nil => simp
  | cons x xs ih =>
    by_cases h : p x <;> cases i <;> simp [takeWhile_cons, h, ih, take_succ_cons]

@[simp] theorem all_takeWhile {l : List α} : (l.takeWhile p).all p = true := by
  induction l with
  | nil => rfl
  | cons h _ ih => by_cases p h <;> simp_all

@[simp] theorem any_dropWhile {l : List α} :
    (l.dropWhile p).any (fun x => !p x) = !l.all p := by
  induction l with
  | nil => rfl
  | cons h _ ih => by_cases p h <;> simp_all

theorem replace_takeWhile [BEq α] [LawfulBEq α] {l : List α} {p : α → Bool} (h : p a = p b) :
    (l.takeWhile p).replace a b = (l.replace a b).takeWhile p := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [takeWhile_cons, replace_cons]
    split <;> rename_i h₁ <;> split <;> rename_i h₂
    · simp_all
    · simp [replace_cons, h₂, takeWhile_cons, h₁, ih]
    · simp_all
    · simp_all

/-! ### splitAt -/

@[simp] theorem splitAt_eq (i : Nat) (l : List α) : splitAt i l = (l.take i, l.drop i) := by
  rw [splitAt, splitAt_go, reverse_nil, nil_append]
  split <;> simp_all [take_of_length_le, drop_of_length_le]

/-! ### rotateLeft -/

@[simp] theorem rotateLeft_zero (l : List α) : rotateLeft l 0 = l := by
  simp [rotateLeft]

-- TODO Batteries defines its own `getElem?_rotate`, which we need to adapt.
-- TODO Prove `map_rotateLeft`, using `ext` and `getElem?_rotateLeft`.

/-! ### rotateRight -/

@[simp] theorem rotateRight_zero (l : List α) : rotateRight l 0 = l := by
  simp [rotateRight]

-- TODO Batteries defines its own `getElem?_rotate`, which we need to adapt.
-- TODO Prove `map_rotateRight`, using `ext` and `getElem?_rotateRight`.

end List
