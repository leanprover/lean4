/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
prelude
import Init.Data.List.Sublist

/-!
# Lemmas about `List.countP` and `List.count`.
-/

-- set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
-- set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace List

open Nat

/-! ### countP -/
section countP

variable (p q : α → Bool)

@[simp] theorem countP_nil : countP p [] = 0 := rfl

protected theorem countP_go_eq_add (l) : countP.go p l n = n + countP.go p l 0 := by
  induction l generalizing n with
  | nil => rfl
  | cons hd _ ih =>
    unfold countP.go
    rw [ih (n := n + 1), ih (n := n), ih (n := 1)]
    if h : p hd then simp [h, Nat.add_assoc] else simp [h]

@[simp] theorem countP_cons_of_pos (l) (pa : p a) : countP p (a :: l) = countP p l + 1 := by
  have : countP.go p (a :: l) 0 = countP.go p l 1 := show cond .. = _ by rw [pa]; rfl
  unfold countP
  rw [this, Nat.add_comm, List.countP_go_eq_add]

@[simp] theorem countP_cons_of_neg (l) (pa : ¬p a) : countP p (a :: l) = countP p l := by
  simp [countP, countP.go, pa]

theorem countP_cons (a : α) (l) : countP p (a :: l) = countP p l + if p a then 1 else 0 := by
  by_cases h : p a <;> simp [h]

@[simp] theorem countP_singleton (a : α) : countP p [a] = if p a then 1 else 0 := by
  simp [countP_cons]

theorem length_eq_countP_add_countP (l) : length l = countP p l + countP (fun a => ¬p a) l := by
  induction l with
  | nil => rfl
  | cons hd _ ih =>
    if h : p hd then
      rw [countP_cons_of_pos _ _ h, countP_cons_of_neg _ _ _, length, ih]
      · rw [Nat.add_assoc, Nat.add_comm _ 1, Nat.add_assoc]
      · simp [h]
    else
      rw [countP_cons_of_pos (fun a => ¬p a) _ _, countP_cons_of_neg _ _ h, length, ih]
      · rfl
      · simp [h]

theorem countP_eq_length_filter (l) : countP p l = length (filter p l) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    if h : p x
    then rw [countP_cons_of_pos p l h, ih, filter_cons_of_pos h, length]
    else rw [countP_cons_of_neg p l h, ih, filter_cons_of_neg h]

theorem countP_eq_length_filter' : countP p = length ∘ filter p := by
  funext l
  apply countP_eq_length_filter

theorem countP_le_length : countP p l ≤ l.length := by
  simp only [countP_eq_length_filter]
  apply length_filter_le

@[simp] theorem countP_append (l₁ l₂) : countP p (l₁ ++ l₂) = countP p l₁ + countP p l₂ := by
  simp only [countP_eq_length_filter, filter_append, length_append]

@[simp] theorem countP_pos_iff {p} : 0 < countP p l ↔ ∃ a ∈ l, p a := by
  simp only [countP_eq_length_filter, length_pos_iff_exists_mem, mem_filter, exists_prop]

@[deprecated countP_pos_iff (since := "2024-09-09")] abbrev countP_pos := @countP_pos_iff

@[simp] theorem one_le_countP_iff {p} : 1 ≤ countP p l ↔ ∃ a ∈ l, p a :=
  countP_pos_iff

@[simp] theorem countP_eq_zero {p} : countP p l = 0 ↔ ∀ a ∈ l, ¬p a := by
  simp only [countP_eq_length_filter, length_eq_zero_iff, filter_eq_nil_iff]

@[simp] theorem countP_eq_length {p} : countP p l = l.length ↔ ∀ a ∈ l, p a := by
  rw [countP_eq_length_filter, filter_length_eq_length]

theorem countP_replicate (p : α → Bool) (a : α) (n : Nat) :
    countP p (replicate n a) = if p a then n else 0 := by
  simp only [countP_eq_length_filter, filter_replicate]
  split <;> simp

theorem boole_getElem_le_countP (p : α → Bool) (l : List α) (i : Nat) (h : i < l.length) :
    (if p l[i] then 1 else 0) ≤ l.countP p := by
  induction l generalizing i with
  | nil => simp at h
  | cons x l ih =>
    cases i with
    | zero => simp [countP_cons]
    | succ i =>
      simp only [length_cons, add_one_lt_add_one_iff] at h
      simp only [getElem_cons_succ, countP_cons]
      specialize ih _ h
      exact le_add_right_of_le ih

theorem Sublist.countP_le (s : l₁ <+ l₂) : countP p l₁ ≤ countP p l₂ := by
  simp only [countP_eq_length_filter]
  apply s.filter _ |>.length_le

theorem IsPrefix.countP_le (s : l₁ <+: l₂) : countP p l₁ ≤ countP p l₂ := s.sublist.countP_le _
theorem IsSuffix.countP_le (s : l₁ <:+ l₂) : countP p l₁ ≤ countP p l₂ := s.sublist.countP_le _
theorem IsInfix.countP_le (s : l₁ <:+: l₂) : countP p l₁ ≤ countP p l₂ := s.sublist.countP_le _

-- See `Init.Data.List.Nat.Count` for `Sublist.le_countP : countP p l₂ - (l₂.length - l₁.length) ≤ countP p l₁`.

theorem countP_tail_le (l) : countP p l.tail ≤ countP p l :=
  (tail_sublist l).countP_le _

-- See `Init.Data.List.Nat.Count` for `le_countP_tail : countP p l - 1 ≤ countP p l.tail`.

theorem countP_filter (l : List α) :
    countP p (filter q l) = countP (fun a => p a && q a) l := by
  simp only [countP_eq_length_filter, filter_filter]

@[simp] theorem countP_true : (countP fun (_ : α) => true) = length := by
  funext l
  simp

@[simp] theorem countP_false : (countP fun (_ : α) => false) = Function.const _ 0 := by
  funext l
  simp

@[simp] theorem countP_map (p : β → Bool) (f : α → β) :
    ∀ l, countP p (map f l) = countP (p ∘ f) l
  | [] => rfl
  | a :: l => by rw [map_cons, countP_cons, countP_cons, countP_map p f l]; rfl

theorem length_filterMap_eq_countP (f : α → Option β) (l : List α) :
    (filterMap f l).length = countP (fun a => (f a).isSome) l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [filterMap_cons, countP_cons]
    split <;> simp [ih, *]

theorem countP_filterMap (p : β → Bool) (f : α → Option β) (l : List α) :
    countP p (filterMap f l) = countP (fun a => ((f a).map p).getD false) l := by
  simp only [countP_eq_length_filter, filter_filterMap, ← filterMap_eq_filter]
  simp only [length_filterMap_eq_countP]
  congr
  ext a
  simp +contextual [Option.getD_eq_iff, Option.isSome_eq_isSome]

@[simp] theorem countP_flatten (l : List (List α)) :
    countP p l.flatten = (l.map (countP p)).sum := by
  simp only [countP_eq_length_filter, filter_flatten]
  simp [countP_eq_length_filter']

@[deprecated countP_flatten (since := "2024-10-14")] abbrev countP_join := @countP_flatten

theorem countP_flatMap (p : β → Bool) (l : List α) (f : α → List β) :
    countP p (l.flatMap f) = sum (map (countP p ∘ f) l) := by
  rw [List.flatMap, countP_flatten, map_map]

@[simp] theorem countP_reverse (l : List α) : countP p l.reverse = countP p l := by
  simp [countP_eq_length_filter, filter_reverse]

variable {p q}

theorem countP_mono_left (h : ∀ x ∈ l, p x → q x) : countP p l ≤ countP q l := by
  induction l with
  | nil => apply Nat.le_refl
  | cons a l ihl =>
    rw [forall_mem_cons] at h
    have ⟨ha, hl⟩ := h
    simp [countP_cons]
    cases h : p a
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      apply Nat.le_trans ?_ (Nat.le_add_right _ _)
      apply ihl hl
    · simp only [↓reduceIte, ha h, succ_le_succ_iff]
      apply ihl hl

theorem countP_congr (h : ∀ x ∈ l, p x ↔ q x) : countP p l = countP q l :=
  Nat.le_antisymm
    (countP_mono_left fun x hx => (h x hx).1)
    (countP_mono_left fun x hx => (h x hx).2)

end countP

/-! ### count -/
section count

variable [BEq α]

@[simp] theorem count_nil (a : α) : count a [] = 0 := rfl

theorem count_cons (a b : α) (l : List α) :
    count a (b :: l) = count a l + if b == a then 1 else 0 := by
  simp [count, countP_cons]

theorem count_eq_countP (a : α) (l : List α) : count a l = countP (· == a) l := rfl
theorem count_eq_countP' {a : α} : count a = countP (· == a) := by
  funext l
  apply count_eq_countP

theorem count_tail : ∀ (l : List α) (a : α) (h : l ≠ []),
      l.tail.count a = l.count a - if l.head h == a then 1 else 0
  | _ :: _, a, _ => by simp [count_cons]

theorem count_le_length (a : α) (l : List α) : count a l ≤ l.length := countP_le_length _

theorem Sublist.count_le (h : l₁ <+ l₂) (a : α) : count a l₁ ≤ count a l₂ := h.countP_le _

theorem IsPrefix.count_le (h : l₁ <+: l₂) (a : α) : count a l₁ ≤ count a l₂ := h.sublist.count_le _
theorem IsSuffix.count_le (h : l₁ <:+ l₂) (a : α) : count a l₁ ≤ count a l₂ := h.sublist.count_le _
theorem IsInfix.count_le (h : l₁ <:+: l₂) (a : α) : count a l₁ ≤ count a l₂ := h.sublist.count_le _

-- See `Init.Data.List.Nat.Count` for `Sublist.le_count : count a l₂ - (l₂.length - l₁.length) ≤ countP a l₁`.

theorem count_tail_le (a : α) (l) : count a l.tail ≤ count a l :=
  (tail_sublist l).count_le _

-- See `Init.Data.List.Nat.Count` for `le_count_tail : count a l - 1 ≤ count a l.tail`.

theorem count_le_count_cons (a b : α) (l : List α) : count a l ≤ count a (b :: l) :=
  (sublist_cons_self _ _).count_le _

theorem count_singleton (a b : α) : count a [b] = if b == a then 1 else 0 := by
  simp [count_cons]

@[simp] theorem count_append (a : α) : ∀ l₁ l₂, count a (l₁ ++ l₂) = count a l₁ + count a l₂ :=
  countP_append _

theorem count_flatten (a : α) (l : List (List α)) : count a l.flatten = (l.map (count a)).sum := by
  simp only [count_eq_countP, countP_flatten, count_eq_countP']

@[deprecated count_flatten (since := "2024-10-14")] abbrev count_join := @count_flatten

@[simp] theorem count_reverse (a : α) (l : List α) : count a l.reverse = count a l := by
  simp only [count_eq_countP, countP_eq_length_filter, filter_reverse, length_reverse]

theorem boole_getElem_le_count (a : α) (l : List α) (i : Nat) (h : i < l.length) :
    (if l[i] == a then 1 else 0) ≤ l.count a := by
  rw [count_eq_countP]
  apply boole_getElem_le_countP (· == a)

variable [LawfulBEq α]

@[simp] theorem count_cons_self (a : α) (l : List α) : count a (a :: l) = count a l + 1 := by
  simp [count_cons]

@[simp] theorem count_cons_of_ne (h : a ≠ b) (l : List α) : count a (b :: l) = count a l := by
  simp only [count_cons, cond_eq_if, beq_iff_eq]
  split <;> simp_all

theorem count_singleton_self (a : α) : count a [a] = 1 := by simp

theorem count_concat_self (a : α) (l : List α) :
    count a (concat l a) = (count a l) + 1 := by simp

@[simp]
theorem count_pos_iff {a : α} {l : List α} : 0 < count a l ↔ a ∈ l := by
  simp only [count, countP_pos_iff, beq_iff_eq, exists_eq_right]

@[deprecated count_pos_iff (since := "2024-09-09")] abbrev count_pos_iff_mem := @count_pos_iff

@[simp] theorem one_le_count_iff {a : α} {l : List α} : 1 ≤ count a l ↔ a ∈ l :=
  count_pos_iff

theorem count_eq_zero_of_not_mem {a : α} {l : List α} (h : a ∉ l) : count a l = 0 :=
  Decidable.byContradiction fun h' => h <| count_pos_iff.1 (Nat.pos_of_ne_zero h')

theorem not_mem_of_count_eq_zero {a : α} {l : List α} (h : count a l = 0) : a ∉ l :=
  fun h' => Nat.ne_of_lt (count_pos_iff.2 h') h.symm

theorem count_eq_zero {l : List α} : count a l = 0 ↔ a ∉ l :=
  ⟨not_mem_of_count_eq_zero, count_eq_zero_of_not_mem⟩

theorem count_eq_length {l : List α} : count a l = l.length ↔ ∀ b ∈ l, a = b := by
  rw [count, countP_eq_length]
  refine ⟨fun h b hb => Eq.symm ?_, fun h b hb => ?_⟩
  · simpa using h b hb
  · rw [h b hb, beq_self_eq_true]

@[simp] theorem count_replicate_self (a : α) (n : Nat) : count a (replicate n a) = n :=
  (count_eq_length.2 <| fun _ h => (eq_of_mem_replicate h).symm).trans (length_replicate ..)

theorem count_replicate (a b : α) (n : Nat) : count a (replicate n b) = if b == a then n else 0 := by
  split <;> (rename_i h; simp only [beq_iff_eq] at h)
  · exact ‹b = a› ▸ count_replicate_self ..
  · exact count_eq_zero.2 <| mt eq_of_mem_replicate (Ne.symm h)

theorem filter_beq (l : List α) (a : α) : l.filter (· == a) = replicate (count a l) a := by
  simp only [count, countP_eq_length_filter, eq_replicate_iff, mem_filter, beq_iff_eq]
  exact ⟨trivial, fun _ h => h.2⟩

theorem filter_eq {α} [DecidableEq α] (l : List α) (a : α) : l.filter (· = a) = replicate (count a l) a :=
  filter_beq l a

theorem le_count_iff_replicate_sublist {l : List α} : n ≤ count a l ↔ replicate n a <+ l := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact ((replicate_sublist_replicate a).2 h).trans <| filter_beq l a ▸ filter_sublist _
  · simpa only [count_replicate_self] using h.count_le a

theorem replicate_count_eq_of_count_eq_length {l : List α} (h : count a l = length l) :
    replicate (count a l) a = l :=
  (le_count_iff_replicate_sublist.mp (Nat.le_refl _)).eq_of_length <|
    (length_replicate (count a l) a).trans h

@[simp] theorem count_filter {l : List α} (h : p a) : count a (filter p l) = count a l := by
  rw [count, countP_filter]; congr; funext b
  simp; rintro rfl; exact h

theorem count_le_count_map [DecidableEq β] (l : List α) (f : α → β) (x : α) :
    count x l ≤ count (f x) (map f l) := by
  rw [count, count, countP_map]
  apply countP_mono_left; simp +contextual

theorem count_filterMap {α} [BEq β] (b : β) (f : α → Option β) (l : List α) :
    count b (filterMap f l) = countP (fun a => f a == some b) l := by
  rw [count_eq_countP, countP_filterMap]
  congr
  ext a
  obtain _ | b := f a
  · simp
  · simp

theorem count_flatMap {α} [BEq β] (l : List α) (f : α → List β) (x : β) :
    count x (l.flatMap f) = sum (map (count x ∘ f) l) := countP_flatMap _ _ _

theorem count_erase (a b : α) :
    ∀ l : List α, count a (l.erase b) = count a l - if b == a then 1 else 0
  | [] => by simp
  | c :: l => by
    rw [erase_cons]
    if hc : c = b then
      have hc_beq := beq_iff_eq.mpr hc
      rw [if_pos hc_beq, hc, count_cons, Nat.add_sub_cancel]
    else
      have hc_beq := beq_false_of_ne hc
      simp only [hc_beq, if_false, count_cons, count_cons, count_erase a b l, reduceCtorEq]
      if ha : b = a then
        rw [ha, eq_comm] at hc
        rw [if_pos (beq_iff_eq.2 ha), if_neg (by simpa using Ne.symm hc), Nat.add_zero, Nat.add_zero]
      else
        rw [if_neg (by simpa using ha), Nat.sub_zero, Nat.sub_zero]

@[simp] theorem count_erase_self (a : α) (l : List α) :
    count a (List.erase l a) = count a l - 1 := by rw [count_erase, if_pos (by simp)]

@[simp] theorem count_erase_of_ne (ab : a ≠ b) (l : List α) : count a (l.erase b) = count a l := by
  rw [count_erase, if_neg (by simpa using ab.symm), Nat.sub_zero]

end count
