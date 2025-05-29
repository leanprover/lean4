
set_option grind.warning false

open List

namespace List'

open Nat

/-! ### countP -/
section countP

variable {p q : α → Bool}

theorem countP_nil : countP p [] = 0 := by grind

theorem countP_cons_of_pos {l} (pa : p a) : countP p (a :: l) = countP p l + 1 := by
  grind

theorem countP_cons_of_neg {l} (pa : ¬p a) : countP p (a :: l) = countP p l := by
  grind

theorem countP_cons {a : α} {l : List α} : countP p (a :: l) = countP p l + if p a then 1 else 0 := List.countP_cons -- This is already a grind lemma

theorem countP_singleton {a : α} : countP p [a] = if p a then 1 else 0 := by grind

example (hx : x = 0) (hy : y = 0) (hz : z = 0) : x = y + z := by grind -- cutsat bug

theorem length_eq_countP_add_countP (p : α → Bool) {l : List α} : length l = countP p l + countP (fun a => ¬p a) l := by
  induction l with grind -- failing because of cutsat bug

theorem countP_eq_length_filter {l : List α} : countP p l = length (filter p l) := by
  induction l with grind

theorem countP_eq_length_filter' : countP p = length ∘ filter p := by
  grind

theorem countP_le_length : countP p l ≤ l.length := by
  grind

theorem countP_append {l₁ l₂ : List α} : countP p (l₁ ++ l₂) = countP p l₁ + countP p l₂ := by
  grind

theorem countP_pos_iff {p} : 0 < countP p l ↔ ∃ a ∈ l, p a := by
  induction l with grind

theorem one_le_countP_iff {p} : 1 ≤ countP p l ↔ ∃ a ∈ l, p a := by
  induction l with grind

theorem countP_eq_zero {p} : countP p l = 0 ↔ ∀ a ∈ l, ¬p a := by
  induction l with grind

theorem countP_eq_length {p} : countP p l = l.length ↔ ∀ a ∈ l, p a := by
  induction l with grind

theorem countP_replicate {p : α → Bool} {a : α} {n : Nat} :
    countP p (replicate n a) = if p a then n else 0 := by
  grind

theorem boole_getElem_le_countP {p : α → Bool} {l : List α} {i : Nat} (h : i < l.length) :
    (if p l[i] then 1 else 0) ≤ l.countP p := by
  induction l generalizing i with grind

theorem Sublist.countP_le (s : l₁ <+ l₂) : countP p l₁ ≤ countP p l₂ := by grind

theorem IsPrefix.countP_le (s : l₁ <+: l₂) : countP p l₁ ≤ countP p l₂ := by grind
theorem IsSuffix.countP_le (s : l₁ <:+ l₂) : countP p l₁ ≤ countP p l₂ := by grind
theorem IsInfix.countP_le (s : l₁ <:+: l₂) : countP p l₁ ≤ countP p l₂ := by grind

-- See `Init.Data.List.Nat.Count` for `Sublist.le_countP : countP p l₂ - (l₂.length - l₁.length) ≤ countP p l₁`.

theorem countP_tail_le (l) : countP p l.tail ≤ countP p l := by grind -- fails

-- See `Init.Data.List.Nat.Count` for `le_countP_tail : countP p l - 1 ≤ countP p l.tail`.

-- TODO Should we have `@[grind]` for `filter_filter`?

theorem countP_filter {l : List α} :
    countP p (filter q l) = countP (fun a => p a && q a) l := by
  grind [List.filter_filter]

theorem countP_true : (countP fun (_ : α) => true) = length := by
  grind -- fails

theorem countP_false : (countP fun (_ : α) => false) = Function.const _ 0 := by
  grind -- fails

theorem countP_map {p : β → Bool} {f : α → β} {l} : countP p (map f l) = countP (p ∘ f) l := by
  grind

theorem length_filterMap_eq_countP {f : α → Option β} {l : List α} :
    (filterMap f l).length = countP (fun a => (f a).isSome) l := by
  induction l with grind

theorem countP_filterMap {p : β → Bool} {f : α → Option β} {l : List α} :
    countP p (filterMap f l) = countP (fun a => ((f a).map p).getD false) l := by
  induction l with grind

theorem countP_flatten {l : List (List α)} :
    countP p l.flatten = (l.map (countP p)).sum := by
  grind

theorem countP_flatMap {p : β → Bool} {l : List α} {f : α → List β} :
    countP p (l.flatMap f) = sum (map (countP p ∘ f) l) := by
  grind

theorem countP_reverse {l : List α} : countP p l.reverse = countP p l := by
  grind

theorem countP_mono_left (h : ∀ x ∈ l, p x → q x) : countP p l ≤ countP q l := by
  induction l with grind

theorem countP_congr (h : ∀ x ∈ l, p x ↔ q x) : countP p l = countP q l := by
  induction l with grind

end countP

/-! ### count -/
section count

variable [BEq α]

theorem count_nil {a : α} : count a [] = 0 := by grind

theorem count_cons {a b : α} {l : List α} :
    count a (b :: l) = count a l + if b == a then 1 else 0 := by grind

theorem count_eq_countP {a : α} {l : List α} : count a l = countP (· == a) l := by grind
theorem count_eq_countP' {a : α} : count a = countP (· == a) := by grind

theorem count_tail {l : List α} (h : l ≠ []) (a : α) :
      l.tail.count a = l.count a - if l.head h == a then 1 else 0 := by grind -- fails

theorem count_le_length {a : α} {l : List α} : count a l ≤ l.length := by grind

theorem Sublist.count_le (a : α) (h : l₁ <+ l₂) : count a l₁ ≤ count a l₂ := by grind

theorem IsPrefix.count_le (a : α) (h : l₁ <+: l₂) : count a l₁ ≤ count a l₂ := by grind
theorem IsSuffix.count_le (a : α) (h : l₁ <:+ l₂) : count a l₁ ≤ count a l₂ := by grind
theorem IsInfix.count_le (a : α) (h : l₁ <:+: l₂) : count a l₁ ≤ count a l₂ := by grind

-- See `Init.Data.List.Nat.Count` for `Sublist.le_count : count a l₂ - (l₂.length - l₁.length) ≤ countP a l₁`.

theorem count_tail_le {a : α} {l : List α} : count a l.tail ≤ count a l := by
  grind -- fails

-- See `Init.Data.List.Nat.Count` for `le_count_tail : count a l - 1 ≤ count a l.tail`.

theorem count_le_count_cons {a b : α} {l : List α} : count a l ≤ count a (b :: l) := by
  grind

theorem count_singleton {a b : α} : count a [b] = if b == a then 1 else 0 := by
  grind

theorem count_append {a : α} {l₁ l₂ : List α} : count a (l₁ ++ l₂) = count a l₁ + count a l₂ := by grind

theorem count_flatten {a : α} {l : List (List α)} : count a l.flatten = (l.map (count a)).sum := by
  grind (ematch := 10) (gen := 10) -- fails

theorem count_reverse {a : α} {l : List α} : count a l.reverse = count a l := by
  grind

theorem boole_getElem_le_count {a : α} {l : List α} {i : Nat} (h : i < l.length) :
    (if l[i] == a then 1 else 0) ≤ l.count a := by
  induction l generalizing i with grind

variable [LawfulBEq α]

theorem count_cons_self {a : α} {l : List α} : count a (a :: l) = count a l + 1 := by
  grind

theorem count_cons_of_ne (h : b ≠ a) {l : List α} : count a (b :: l) = count a l := by
  grind

theorem count_singleton_self {a : α} : count a [a] = 1 := by grind

theorem count_concat_self {a : α} {l : List α} : count a (concat l a) = count a l + 1 := by grind [concat_eq_append] -- fails?!

theorem count_pos_iff {a : α} {l : List α} : 0 < count a l ↔ a ∈ l := by
  induction l with grind -- fails

theorem one_le_count_iff {a : α} {l : List α} : 1 ≤ count a l ↔ a ∈ l := by
  induction l with grind -- fails

theorem count_eq_zero_of_not_mem {a : α} {l : List α} (h : a ∉ l) : count a l = 0 := by
  induction l with grind

theorem not_mem_of_count_eq_zero {a : α} {l : List α} (h : count a l = 0) : a ∉ l := by
  induction l with grind

theorem count_eq_zero {l : List α} : count a l = 0 ↔ a ∉ l := by
  induction l with grind -- fails

theorem count_eq_length {l : List α} : count a l = l.length ↔ ∀ b ∈ l, a = b := by
  induction l with grind

-- WIP

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
