/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
module

prelude
import Init.Data.List.Sublist

/-!
# Lemmas about `List.countP` and `List.count`.

Because we mark `countP_eq_length_filter` and `count_eq_countP` with `@[grind _=_]`,
we don't need many other `@[grind]` annotations here.
-/

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace List

open Nat

/-! ### countP -/
section countP

variable {p q : α → Bool}

@[simp] theorem countP_nil : countP p [] = 0 := rfl

protected theorem countP_go_eq_add {l} : countP.go p l n = n + countP.go p l 0 := by
  induction l generalizing n with
  | nil => rfl
  | cons hd _ ih =>
    unfold countP.go
    rw [ih (n := n + 1), ih (n := n), ih (n := 1)]
    if h : p hd then simp [h, Nat.add_assoc] else simp [h]

@[simp] theorem countP_cons_of_pos {l} (pa : p a) : countP p (a :: l) = countP p l + 1 := by
  have : countP.go p (a :: l) 0 = countP.go p l 1 := show cond .. = _ by rw [pa]; rfl
  unfold countP
  rw [this, Nat.add_comm, List.countP_go_eq_add]

@[simp] theorem countP_cons_of_neg {l} (pa : ¬p a) : countP p (a :: l) = countP p l := by
  simp [countP, countP.go, pa]

theorem countP_cons {a : α} {l : List α} : countP p (a :: l) = countP p l + if p a then 1 else 0 := by
  by_cases h : p a <;> simp [h]

@[simp] theorem countP_singleton {a : α} : countP p [a] = if p a then 1 else 0 := by
  simp [countP_cons]

theorem length_eq_countP_add_countP (p : α → Bool) {l : List α} : length l = countP p l + countP (fun a => ¬p a) l := by
  induction l with
  | nil => rfl
  | cons hd _ ih =>
    if h : p hd then
      rw [countP_cons_of_pos h, countP_cons_of_neg _, length, ih]
      · rw [Nat.add_assoc, Nat.add_comm _ 1, Nat.add_assoc]
      · simp [h]
    else
      rw [countP_cons_of_pos (p := fun a => ¬p a), countP_cons_of_neg h, length, ih]
      · rfl
      · simp [h]

@[grind _=_]  -- This to quite aggressive, as it introduces `filter` based reasoning whenever we see `countP`.
theorem countP_eq_length_filter {l : List α} : countP p l = (filter p l).length := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    if h : p x
    then rw [countP_cons_of_pos h, ih, filter_cons_of_pos h, length]
    else rw [countP_cons_of_neg h, ih, filter_cons_of_neg h]

@[grind =]
theorem countP_eq_length_filter' : countP p = length ∘ filter p := by
  funext l
  apply countP_eq_length_filter

theorem countP_le_length : countP p l ≤ l.length := by
  simp only [countP_eq_length_filter]
  apply length_filter_le

@[simp, grind =] theorem countP_append {l₁ l₂ : List α} : countP p (l₁ ++ l₂) = countP p l₁ + countP p l₂ := by
  simp only [countP_eq_length_filter, filter_append, length_append]

@[simp] theorem countP_pos_iff {p} : 0 < countP p l ↔ ∃ a ∈ l, p a := by
  simp only [countP_eq_length_filter, length_pos_iff_exists_mem, mem_filter, exists_prop]

@[simp] theorem one_le_countP_iff {p} : 1 ≤ countP p l ↔ ∃ a ∈ l, p a :=
  countP_pos_iff

@[simp] theorem countP_eq_zero {p} : countP p l = 0 ↔ ∀ a ∈ l, ¬p a := by
  simp only [countP_eq_length_filter, length_eq_zero_iff, filter_eq_nil_iff]

@[simp] theorem countP_eq_length {p} : countP p l = l.length ↔ ∀ a ∈ l, p a := by
  rw [countP_eq_length_filter, length_filter_eq_length_iff]

theorem countP_replicate {p : α → Bool} {a : α} {n : Nat} :
    countP p (replicate n a) = if p a then n else 0 := by
  simp only [countP_eq_length_filter, filter_replicate]
  split <;> simp

@[grind]
theorem boole_getElem_le_countP {p : α → Bool} {l : List α} {i : Nat} (h : i < l.length) :
    (if p l[i] then 1 else 0) ≤ l.countP p := by
  induction l generalizing i with
  | nil => simp at h
  | cons x l ih =>
    cases i with
    | zero => simp [countP_cons]
    | succ i =>
      simp only [length_cons, add_one_lt_add_one_iff] at h
      simp only [getElem_cons_succ, countP_cons]
      specialize ih h
      exact le_add_right_of_le ih

theorem Sublist.countP_le (s : l₁ <+ l₂) : countP p l₁ ≤ countP p l₂ := by
  simp only [countP_eq_length_filter]
  apply s.filter _ |>.length_le

grind_pattern Sublist.countP_le => l₁ <+ l₂, countP p l₁
grind_pattern Sublist.countP_le => l₁ <+ l₂, countP p l₂

theorem IsPrefix.countP_le (s : l₁ <+: l₂) : countP p l₁ ≤ countP p l₂ := s.sublist.countP_le

grind_pattern IsPrefix.countP_le => l₁ <+: l₂, countP p l₁
grind_pattern IsPrefix.countP_le => l₁ <+: l₂, countP p l₂

theorem IsSuffix.countP_le (s : l₁ <:+ l₂) : countP p l₁ ≤ countP p l₂ := s.sublist.countP_le

grind_pattern IsSuffix.countP_le => l₁ <:+ l₂, countP p l₁
grind_pattern IsSuffix.countP_le => l₁ <:+ l₂, countP p l₂

theorem IsInfix.countP_le (s : l₁ <:+: l₂) : countP p l₁ ≤ countP p l₂ := s.sublist.countP_le

grind_pattern IsInfix.countP_le => l₁ <:+: l₂, countP p l₁
grind_pattern IsInfix.countP_le => l₁ <:+: l₂, countP p l₂

-- See `Init.Data.List.Nat.Count` for `Sublist.le_countP : countP p l₂ - (l₂.length - l₁.length) ≤ countP p l₁`.

@[grind]
theorem countP_tail_le (l) : countP p l.tail ≤ countP p l :=
  (tail_sublist l).countP_le

-- See `Init.Data.List.Nat.Count` for `le_countP_tail : countP p l - 1 ≤ countP p l.tail`.

theorem countP_filter {l : List α} :
    countP p (filter q l) = countP (fun a => p a && q a) l := by
  simp only [countP_eq_length_filter, filter_filter]

@[simp] theorem countP_true : (countP fun (_ : α) => true) = length := by
  funext l
  simp

@[simp] theorem countP_false : (countP fun (_ : α) => false) = Function.const _ 0 := by
  funext l
  simp

@[simp] theorem countP_map {p : β → Bool} {f : α → β} :
    ∀ {l}, countP p (map f l) = countP (p ∘ f) l
  | [] => rfl
  | a :: l => by rw [map_cons, countP_cons, countP_cons, countP_map]; rfl

theorem length_filterMap_eq_countP {f : α → Option β} {l : List α} :
    (filterMap f l).length = countP (fun a => (f a).isSome) l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [filterMap_cons, countP_cons]
    split <;> simp [ih, *]

theorem countP_filterMap {p : β → Bool} {f : α → Option β} {l : List α} :
    countP p (filterMap f l) = countP (fun a => ((f a).map p).getD false) l := by
  simp only [countP_eq_length_filter, filter_filterMap, ← filterMap_eq_filter]
  simp only [length_filterMap_eq_countP]
  congr
  ext a
  cases h : f a <;> simp_all [Option.isSome_filter]

@[simp] theorem countP_flatten {l : List (List α)} :
    countP p l.flatten = (l.map (countP p)).sum := by
  simp only [countP_eq_length_filter, filter_flatten]
  simp [countP_eq_length_filter']

theorem countP_flatMap {p : β → Bool} {l : List α} {f : α → List β} :
    countP p (l.flatMap f) = sum (map (countP p ∘ f) l) := by
  rw [List.flatMap, countP_flatten, map_map]

@[simp, grind =] theorem countP_reverse {l : List α} : countP p l.reverse = countP p l := by
  simp [countP_eq_length_filter, filter_reverse]

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

@[simp, grind =] theorem count_nil {a : α} : count a [] = 0 := rfl

@[grind]
theorem count_cons {a b : α} {l : List α} :
    count a (b :: l) = count a l + if b == a then 1 else 0 := by
  simp [count, countP_cons]

theorem count_eq_countP {a : α} {l : List α} : count a l = countP (· == a) l := rfl
theorem count_eq_countP' {a : α} : count a = countP (· == a) := by
  funext l
  apply count_eq_countP

@[grind =]
theorem count_eq_length_filter {a : α} {l : List α} : count a l = (filter (· == a) l).length := by
  simp [count, countP_eq_length_filter]

@[grind]
theorem count_tail : ∀ {l : List α} {a : α},
      l.tail.count a = l.count a - if l.head? == some a then 1 else 0
  | [], a => by simp
  | _ :: _, a => by simp [count_cons]

theorem count_le_length {a : α} {l : List α} : count a l ≤ l.length := countP_le_length

grind_pattern count_le_length => count a l

theorem Sublist.count_le (a : α) (h : l₁ <+ l₂) : count a l₁ ≤ count a l₂ := h.countP_le

grind_pattern Sublist.count_le => l₁ <+ l₂, count a l₁
grind_pattern Sublist.count_le => l₁ <+ l₂, count a l₂

theorem IsPrefix.count_le (a : α) (h : l₁ <+: l₂) : count a l₁ ≤ count a l₂ := h.sublist.count_le a

grind_pattern IsPrefix.count_le => l₁ <+: l₂, count a l₁
grind_pattern IsPrefix.count_le => l₁ <+: l₂, count a l₂

theorem IsSuffix.count_le (a : α) (h : l₁ <:+ l₂) : count a l₁ ≤ count a l₂ := h.sublist.count_le a

grind_pattern IsSuffix.count_le => l₁ <:+ l₂, count a l₁
grind_pattern IsSuffix.count_le => l₁ <:+ l₂, count a l₂

theorem IsInfix.count_le (a : α) (h : l₁ <:+: l₂) : count a l₁ ≤ count a l₂ := h.sublist.count_le a

grind_pattern IsInfix.count_le => l₁ <:+: l₂, count a l₁
grind_pattern IsInfix.count_le => l₁ <:+: l₂, count a l₂

-- See `Init.Data.List.Nat.Count` for `Sublist.le_count : count a l₂ - (l₂.length - l₁.length) ≤ countP a l₁`.

theorem count_tail_le {a : α} {l : List α} : count a l.tail ≤ count a l :=
  (tail_sublist l).count_le a

-- See `Init.Data.List.Nat.Count` for `le_count_tail : count a l - 1 ≤ count a l.tail`.

theorem count_le_count_cons {a b : α} {l : List α} : count a l ≤ count a (b :: l) :=
  (sublist_cons_self _ _).count_le a

theorem count_singleton {a b : α} : count a [b] = if b == a then 1 else 0 := by
  simp [count_cons]

@[simp, grind =] theorem count_append {a : α} {l₁ l₂ : List α} : count a (l₁ ++ l₂) = count a l₁ + count a l₂ :=
  countP_append

@[grind =]
theorem count_flatten {a : α} {l : List (List α)} : count a l.flatten = (l.map (count a)).sum := by
  simp only [count_eq_countP, countP_flatten, count_eq_countP']

@[simp, grind =] theorem count_reverse {a : α} {l : List α} : count a l.reverse = count a l := by
  simp only [count_eq_countP, countP_eq_length_filter, filter_reverse, length_reverse]

@[grind]
theorem boole_getElem_le_count {a : α} {l : List α} {i : Nat} (h : i < l.length) :
    (if l[i] == a then 1 else 0) ≤ l.count a := by
  rw [count_eq_countP]
  apply boole_getElem_le_countP (p := (· == a))

variable [LawfulBEq α]

@[simp] theorem count_cons_self {a : α} {l : List α} : count a (a :: l) = count a l + 1 := by
  simp [count_cons]

@[simp] theorem count_cons_of_ne (h : b ≠ a) {l : List α} : count a (b :: l) = count a l := by
  simp [count_cons, h]

theorem count_singleton_self {a : α} : count a [a] = 1 := by simp

theorem count_concat_self {a : α} {l : List α} : count a (concat l a) = count a l + 1 := by simp

@[simp]
theorem count_pos_iff {a : α} {l : List α} : 0 < count a l ↔ a ∈ l := by
  simp only [count, countP_pos_iff, beq_iff_eq, exists_eq_right]

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

@[simp] theorem count_replicate_self {a : α} {n : Nat} : count a (replicate n a) = n :=
  (count_eq_length.2 <| fun _ h => (eq_of_mem_replicate h).symm).trans (length_replicate ..)

@[grind =] theorem count_replicate {a b : α} {n : Nat} : count a (replicate n b) = if b == a then n else 0 := by
  split <;> (rename_i h; simp only [beq_iff_eq] at h)
  · exact ‹b = a› ▸ count_replicate_self ..
  · exact count_eq_zero.2 <| mt eq_of_mem_replicate (Ne.symm h)

theorem filter_beq {l : List α} (a : α) : l.filter (· == a) = replicate (count a l) a := by
  simp only [count, countP_eq_length_filter, eq_replicate_iff, mem_filter, beq_iff_eq]
  exact ⟨trivial, fun _ h => h.2⟩

theorem filter_eq [DecidableEq α] {l : List α} (a : α) : l.filter (· = a) = replicate (count a l) a :=
  funext (Bool.beq_eq_decide_eq · a) ▸ filter_beq a

@[grind =] theorem replicate_sublist_iff {l : List α} : replicate n a <+ l ↔ n ≤ count a l := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simpa only [count_replicate_self] using h.count_le a
  · exact ((replicate_sublist_replicate a).2 h).trans <| filter_beq a ▸ filter_sublist

@[deprecated replicate_sublist_iff (since := "2025-05-26")]
theorem le_count_iff_replicate_sublist {l : List α} : n ≤ count a l ↔ replicate n a <+ l :=
  replicate_sublist_iff.symm

theorem replicate_count_eq_of_count_eq_length {l : List α} (h : count a l = length l) :
    replicate (count a l) a = l :=
  (replicate_sublist_iff.mpr (Nat.le_refl _)).eq_of_length <| length_replicate.trans h

@[simp] theorem count_filter {l : List α} (h : p a) : count a (filter p l) = count a l := by
  rw [count, countP_filter]; congr; funext b
  simp; rintro rfl; exact h

theorem count_le_count_map {β} [BEq β] [LawfulBEq β] {l : List α} {f : α → β} {x : α} :
    count x l ≤ count (f x) (map f l) := by
  rw [count, count, countP_map]
  apply countP_mono_left; simp +contextual

theorem count_filterMap {α} [BEq β] {b : β} {f : α → Option β} {l : List α} :
    count b (filterMap f l) = countP (fun a => f a == some b) l := by
  rw [count_eq_countP, countP_filterMap]
  congr
  ext a
  obtain _ | b := f a
  · simp
  · simp

theorem count_flatMap {α} [BEq β] {l : List α} {f : α → List β} {x : β} :
    count x (l.flatMap f) = sum (map (count x ∘ f) l) := countP_flatMap

@[grind]
theorem count_erase {a b : α} :
    ∀ {l : List α}, count a (l.erase b) = count a l - if b == a then 1 else 0
  | [] => by simp
  | c :: l => by
    rw [erase_cons]
    if hc : c = b then
      have hc_beq := beq_iff_eq.mpr hc
      rw [if_pos hc_beq, hc, count_cons, Nat.add_sub_cancel]
    else
      have hc_beq := beq_false_of_ne hc
      simp only [hc_beq, if_false, count_cons, count_cons, count_erase, reduceCtorEq]
      if ha : b = a then
        rw [ha, eq_comm] at hc
        rw [if_pos (beq_iff_eq.2 ha), if_neg (by simpa using Ne.symm hc), Nat.add_zero, Nat.add_zero]
      else
        rw [if_neg (by simpa using ha), Nat.sub_zero, Nat.sub_zero]

@[simp] theorem count_erase_self {a : α} {l : List α} :
    count a (List.erase l a) = count a l - 1 := by rw [count_erase, if_pos (by simp)]

@[simp] theorem count_erase_of_ne (ab : a ≠ b) {l : List α} : count a (l.erase b) = count a l := by
  rw [count_erase, if_neg (by simpa using ab.symm), Nat.sub_zero]

end count
