/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro,
  Yury Kudryashov
-/
prelude
import Init.Data.List.Pairwise

/-!
# Lemmas about `List.eraseP` and `List.erase`.
-/

namespace List

open Nat

/-! ### eraseP -/

@[simp] theorem eraseP_nil : [].eraseP p = [] := rfl

theorem eraseP_cons (a : α) (l : List α) :
    (a :: l).eraseP p = bif p a then l else a :: l.eraseP p := rfl

@[simp] theorem eraseP_cons_of_pos {l : List α} {p} (h : p a) : (a :: l).eraseP p = l := by
  simp [eraseP_cons, h]

@[simp] theorem eraseP_cons_of_neg {l : List α} {p} (h : ¬p a) :
    (a :: l).eraseP p = a :: l.eraseP p := by simp [eraseP_cons, h]

theorem eraseP_of_forall_not {l : List α} (h : ∀ a, a ∈ l → ¬p a) : l.eraseP p = l := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp [h _ (.head ..), ih (forall_mem_cons.1 h).2]

theorem exists_of_eraseP : ∀ {l : List α} {a} (al : a ∈ l) (pa : p a),
    ∃ a l₁ l₂, (∀ b ∈ l₁, ¬p b) ∧ p a ∧ l = l₁ ++ a :: l₂ ∧ l.eraseP p = l₁ ++ l₂
  | b :: l, a, al, pa =>
    if pb : p b then
      ⟨b, [], l, forall_mem_nil _, pb, by simp [pb]⟩
    else
      match al with
      | .head .. => nomatch pb pa
      | .tail _ al =>
        let ⟨c, l₁, l₂, h₁, h₂, h₃, h₄⟩ := exists_of_eraseP al pa
        ⟨c, b::l₁, l₂, (forall_mem_cons ..).2 ⟨pb, h₁⟩,
          h₂, by rw [h₃, cons_append], by simp [pb, h₄]⟩

theorem exists_or_eq_self_of_eraseP (p) (l : List α) :
    l.eraseP p = l ∨
    ∃ a l₁ l₂, (∀ b ∈ l₁, ¬p b) ∧ p a ∧ l = l₁ ++ a :: l₂ ∧ l.eraseP p = l₁ ++ l₂ :=
  if h : ∃ a ∈ l, p a then
    let ⟨_, ha, pa⟩ := h
    .inr (exists_of_eraseP ha pa)
  else
    .inl (eraseP_of_forall_not (h ⟨·, ·, ·⟩))

@[simp] theorem length_eraseP_of_mem (al : a ∈ l) (pa : p a) :
    length (l.eraseP p) = length l - 1 := by
  let ⟨_, l₁, l₂, _, _, e₁, e₂⟩ := exists_of_eraseP al pa
  rw [e₂]; simp [length_append, e₁]; rfl

theorem length_eraseP {l : List α} : (l.eraseP p).length = if l.any p then l.length - 1 else l.length := by
  split <;> rename_i h
  · simp only [any_eq_true] at h
    obtain ⟨x, m, h⟩ := h
    simp [length_eraseP_of_mem m h]
  · simp only [any_eq_true] at h
    rw [eraseP_of_forall_not]
    simp_all

theorem eraseP_sublist (l : List α) : l.eraseP p <+ l := by
  match exists_or_eq_self_of_eraseP p l with
  | .inl h => rw [h]; apply Sublist.refl
  | .inr ⟨c, l₁, l₂, _, _, h₃, h₄⟩ => rw [h₄, h₃]; simp

theorem eraseP_subset (l : List α) : l.eraseP p ⊆ l := (eraseP_sublist l).subset

protected theorem Sublist.eraseP : l₁ <+ l₂ → l₁.eraseP p <+ l₂.eraseP p
  | .slnil => Sublist.refl _
  | .cons a s => by
    by_cases h : p a
    · simpa [h] using s.eraseP.trans (eraseP_sublist _)
    · simpa [h] using s.eraseP.cons _
  | .cons₂ a s => by
    by_cases h : p a
    · simpa [h] using s
    · simpa [h] using s.eraseP

theorem length_eraseP_le (l : List α) : (l.eraseP p).length ≤ l.length :=
  l.eraseP_sublist.length_le

theorem mem_of_mem_eraseP {l : List α} : a ∈ l.eraseP p → a ∈ l := (eraseP_subset _ ·)

@[simp] theorem mem_eraseP_of_neg {l : List α} (pa : ¬p a) : a ∈ l.eraseP p ↔ a ∈ l := by
  refine ⟨mem_of_mem_eraseP, fun al => ?_⟩
  match exists_or_eq_self_of_eraseP p l with
  | .inl h => rw [h]; assumption
  | .inr ⟨c, l₁, l₂, h₁, h₂, h₃, h₄⟩ =>
    rw [h₄]; rw [h₃] at al
    have : a ≠ c := fun h => (h ▸ pa).elim h₂
    simp [this] at al; simp [al]

@[simp] theorem eraseP_eq_self_iff {p} {l : List α} : l.eraseP p = l ↔ ∀ a ∈ l, ¬ p a := by
  rw [← Sublist.length_eq (eraseP_sublist l), length_eraseP]
  split <;> rename_i h
  · simp only [any_eq_true, length_eq_zero] at h
    constructor
    · intro; simp_all [Nat.sub_one_eq_self]
    · intro; obtain ⟨x, m, h⟩ := h; simp_all
  · simp_all

theorem eraseP_map (f : β → α) : ∀ (l : List β), (map f l).eraseP p = map f (l.eraseP (p ∘ f))
  | [] => rfl
  | b::l => by by_cases h : p (f b) <;> simp [h, eraseP_map f l, eraseP_cons_of_pos]

theorem eraseP_filterMap (f : α → Option β) : ∀ (l : List α),
    (filterMap f l).eraseP p = filterMap f (l.eraseP (fun x => match f x with | some y => p y | none => false))
  | [] => rfl
  | a::l => by
    rw [filterMap_cons, eraseP_cons]
    split <;> rename_i h
    · simp [h, eraseP_filterMap]
    · rename_i b
      rw [h, eraseP_cons]
      by_cases w : p b
      · simp [w]
      · simp only [w, cond_false]
        rw [filterMap_cons_some h, eraseP_filterMap]

theorem eraseP_filter (f : α → Bool) (l : List α) :
    (filter f l).eraseP p = filter f (l.eraseP (fun x => p x && f x)) := by
  rw [← filterMap_eq_filter, eraseP_filterMap]
  congr
  ext x
  simp only [Option.guard]
  split <;> split at * <;> simp_all

theorem eraseP_append_left {a : α} (pa : p a) :
    ∀ {l₁ : List α} l₂, a ∈ l₁ → (l₁++l₂).eraseP p = l₁.eraseP p ++ l₂
  | x :: xs, l₂, h => by
    by_cases h' : p x <;> simp [h']
    rw [eraseP_append_left pa l₂ ((mem_cons.1 h).resolve_left (mt _ h'))]
    intro | rfl => exact pa

theorem eraseP_append_right :
    ∀ {l₁ : List α} l₂, (∀ b ∈ l₁, ¬p b) → eraseP p (l₁++l₂) = l₁ ++ l₂.eraseP p
  | [],      l₂, _ => rfl
  | x :: xs, l₂, h => by
    simp [(forall_mem_cons.1 h).1, eraseP_append_right _ (forall_mem_cons.1 h).2]

theorem eraseP_append (l₁ l₂ : List α) :
    (l₁ ++ l₂).eraseP p = if l₁.any p then l₁.eraseP p ++ l₂ else l₁ ++ l₂.eraseP p := by
  split <;> rename_i h
  · simp only [any_eq_true] at h
    obtain ⟨x, m, h⟩ := h
    rw [eraseP_append_left h _ m]
  · simp only [any_eq_true] at h
    rw [eraseP_append_right _]
    simp_all

theorem eraseP_eq_iff {p} {l : List α} :
    l.eraseP p = l' ↔
      ((∀ a ∈ l, ¬ p a) ∧ l = l') ∨
        ∃ a l₁ l₂, (∀ b ∈ l₁, ¬ p b) ∧ p a ∧ l = l₁ ++ a :: l₂ ∧ l' = l₁ ++ l₂ := by
  cases exists_or_eq_self_of_eraseP p l with
  | inl h =>
    constructor
    · intro h'
      left
      exact ⟨eraseP_eq_self_iff.1 h, by simp_all⟩
    · rintro (⟨-, rfl⟩ | ⟨a, l₁, l₂, h₁, h₂, rfl, rfl⟩)
      · assumption
      · rw [eraseP_append_right _ h₁, eraseP_cons_of_pos h₂]
  | inr h =>
    obtain ⟨a, l₁, l₂, h₁, h₂, w₁, w₂⟩ := h
    rw [w₂]
    subst w₁
    constructor
    · rintro rfl
      right
      refine ⟨a, l₁, l₂, ?_⟩
      simp_all
    · rintro (h | h)
      · simp_all
      · obtain ⟨a', l₁', l₂', h₁', h₂', h, rfl⟩ := h
        have p : l₁ = l₁' := by
          have q : l₁ = takeWhile (fun x => !p x) (l₁ ++ a :: l₂) := by
            rw [takeWhile_append_of_pos (by simp_all),
              takeWhile_cons_of_neg (by simp [h₂]), append_nil]
          have q' : l₁' = takeWhile (fun x => !p x) (l₁' ++ a' :: l₂') := by
            rw [takeWhile_append_of_pos (by simpa using h₁'),
              takeWhile_cons_of_neg (by simp [h₂']), append_nil]
          simp [h] at q
          rw [q', q]
        subst p
        simp_all

@[simp] theorem eraseP_replicate_of_pos {n : Nat} {a : α} (h : p a) :
    (replicate n a).eraseP p = replicate (n - 1) a := by
  cases n <;> simp [replicate_succ, h]

@[simp] theorem eraseP_replicate_of_neg {n : Nat} {a : α} (h : ¬p a) :
    (replicate n a).eraseP p = replicate n a := by
  rw [eraseP_of_forall_not (by simp_all)]

theorem Nodup.eraseP (p) : Nodup l → Nodup (l.eraseP p) :=
  Nodup.sublist <| eraseP_sublist _

theorem eraseP_comm {l : List α} (h : ∀ a ∈ l, ¬ p a ∨ ¬ q a) :
    (l.eraseP p).eraseP q = (l.eraseP q).eraseP p := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [eraseP_cons]
    by_cases h₁ : p a
    · by_cases h₂ : q a
      · simp_all
      · simp [h₁, h₂, ih (fun b m => h b (mem_cons_of_mem _ m))]
    · by_cases h₂ : q a
      · simp [h₁, h₂, ih (fun b m => h b (mem_cons_of_mem _ m))]
      · simp [h₁, h₂, ih (fun b m => h b (mem_cons_of_mem _ m))]

/-! ### erase -/
section erase
variable [BEq α]

@[simp] theorem erase_cons_head [LawfulBEq α] (a : α) (l : List α) : (a :: l).erase a = l := by
  simp [erase_cons]

@[simp] theorem erase_cons_tail {a b : α} {l : List α} (h : ¬(b == a)) :
    (b :: l).erase a = b :: l.erase a := by simp only [erase_cons, if_neg h]

theorem erase_of_not_mem [LawfulBEq α] {a : α} : ∀ {l : List α}, a ∉ l → l.erase a = l
  | [], _ => rfl
  | b :: l, h => by
    rw [mem_cons, not_or] at h
    simp only [erase_cons, if_neg, erase_of_not_mem h.2, beq_iff_eq, Ne.symm h.1, not_false_eq_true]

theorem erase_eq_eraseP' (a : α) (l : List α) : l.erase a = l.eraseP (· == a) := by
  induction l
  · simp
  · next b t ih =>
    rw [erase_cons, eraseP_cons, ih]
    if h : b == a then simp [h] else simp [h]

theorem erase_eq_eraseP [LawfulBEq α] (a : α) : ∀ l : List α,  l.erase a = l.eraseP (a == ·)
  | [] => rfl
  | b :: l => by
    if h : a = b then simp [h] else simp [h, Ne.symm h, erase_eq_eraseP a l]

theorem exists_erase_eq [LawfulBEq α] {a : α} {l : List α} (h : a ∈ l) :
    ∃ l₁ l₂, a ∉ l₁ ∧ l = l₁ ++ a :: l₂ ∧ l.erase a = l₁ ++ l₂ := by
  let ⟨_, l₁, l₂, h₁, e, h₂, h₃⟩ := exists_of_eraseP h (beq_self_eq_true _)
  rw [erase_eq_eraseP]; exact ⟨l₁, l₂, fun h => h₁ _ h (beq_self_eq_true _), eq_of_beq e ▸ h₂, h₃⟩

@[simp] theorem length_erase_of_mem [LawfulBEq α] {a : α} {l : List α} (h : a ∈ l) :
    length (l.erase a) = length l - 1 := by
  rw [erase_eq_eraseP]; exact length_eraseP_of_mem h (beq_self_eq_true a)

theorem length_erase [LawfulBEq α] (a : α) (l : List α) :
    length (l.erase a) = if a ∈ l then length l - 1 else length l := by
  rw [erase_eq_eraseP, length_eraseP]
  split <;> split <;> simp_all

theorem erase_sublist (a : α) (l : List α) : l.erase a <+ l :=
  erase_eq_eraseP' a l ▸ eraseP_sublist ..

theorem erase_subset (a : α) (l : List α) : l.erase a ⊆ l := (erase_sublist a l).subset

theorem Sublist.erase (a : α) {l₁ l₂ : List α} (h : l₁ <+ l₂) : l₁.erase a <+ l₂.erase a := by
  simp only [erase_eq_eraseP']; exact h.eraseP

theorem length_erase_le (a : α) (l : List α) : (l.erase a).length ≤ l.length :=
  (erase_sublist a l).length_le

theorem mem_of_mem_erase {a b : α} {l : List α} (h : a ∈ l.erase b) : a ∈ l := erase_subset _ _ h

@[simp] theorem mem_erase_of_ne [LawfulBEq α] {a b : α} {l : List α} (ab : a ≠ b) :
    a ∈ l.erase b ↔ a ∈ l :=
  erase_eq_eraseP b l ▸ mem_eraseP_of_neg (mt eq_of_beq ab.symm)

@[simp] theorem erase_eq_self_iff [LawfulBEq α] {l : List α} : l.erase a = l ↔ a ∉ l := by
  rw [erase_eq_eraseP', eraseP_eq_self_iff]
  simp

theorem erase_filter [LawfulBEq α] (f : α → Bool) (l : List α) :
    (filter f l).erase a = filter f (l.erase a) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : a = x
    · rw [erase_cons]
      simp only [h, beq_self_eq_true, ↓reduceIte]
      rw [filter_cons]
      split
      · rw [erase_cons_head]
      · rw [erase_of_not_mem]
        simp_all [mem_filter]
    · rw [erase_cons_tail (by simpa using Ne.symm h), filter_cons, filter_cons]
      split
      · rw [erase_cons_tail (by simpa using Ne.symm h), ih]
      · rw [ih]

theorem erase_append_left [LawfulBEq α] {l₁ : List α} (l₂) (h : a ∈ l₁) :
    (l₁ ++ l₂).erase a = l₁.erase a ++ l₂ := by
  simp [erase_eq_eraseP]; exact eraseP_append_left (beq_self_eq_true a) l₂ h

theorem erase_append_right [LawfulBEq α] {a : α} {l₁ : List α} (l₂ : List α) (h : a ∉ l₁) :
    (l₁ ++ l₂).erase a = (l₁ ++ l₂.erase a) := by
  rw [erase_eq_eraseP, erase_eq_eraseP, eraseP_append_right]
  intros b h' h''; rw [eq_of_beq h''] at h; exact h h'

theorem erase_append [LawfulBEq α] {a : α} {l₁ l₂ : List α} :
    (l₁ ++ l₂).erase a = if a ∈ l₁ then l₁.erase a ++ l₂ else l₁ ++ l₂.erase a := by
  simp [erase_eq_eraseP, eraseP_append]

theorem erase_comm [LawfulBEq α] (a b : α) (l : List α) :
    (l.erase a).erase b = (l.erase b).erase a := by
  if ab : a == b then rw [eq_of_beq ab] else ?_
  if ha : a ∈ l then ?_ else
    simp only [erase_of_not_mem ha, erase_of_not_mem (mt mem_of_mem_erase ha)]
  if hb : b ∈ l then ?_ else
    simp only [erase_of_not_mem hb, erase_of_not_mem (mt mem_of_mem_erase hb)]
  match l, l.erase a, exists_erase_eq ha with
  | _, _, ⟨l₁, l₂, ha', rfl, rfl⟩ =>
    if h₁ : b ∈ l₁ then
      rw [erase_append_left _ h₁, erase_append_left _ h₁,
          erase_append_right _ (mt mem_of_mem_erase ha'), erase_cons_head]
    else
      rw [erase_append_right _ h₁, erase_append_right _ h₁, erase_append_right _ ha',
          erase_cons_tail ab, erase_cons_head]

theorem erase_eq_iff [LawfulBEq α] {a : α} {l : List α} :
    l.erase a = l' ↔
      (a ∉ l ∧ l = l') ∨
        ∃ l₁ l₂, a ∉ l₁ ∧ l = l₁ ++ a :: l₂ ∧ l' = l₁ ++ l₂ := by
  rw [erase_eq_eraseP', eraseP_eq_iff]
  simp only [beq_iff_eq, forall_mem_ne', exists_and_left]
  constructor
  · rintro (⟨h, rfl⟩ | ⟨a', l', h, rfl, x, rfl, rfl⟩)
    · left; simp_all
    · right; refine ⟨l', h, x, by simp⟩
  · rintro (⟨h, rfl⟩ | ⟨l₁, h, x, rfl, rfl⟩)
    · left; simp_all
    · right; refine ⟨a, l₁, h, by simp⟩

@[simp] theorem erase_replicate_self [LawfulBEq α] {a : α} :
    (replicate n a).erase a = replicate (n - 1) a := by
  cases n <;> simp [replicate_succ]

@[simp] theorem erase_replicate_ne [LawfulBEq α] {a b : α} (h : !b == a) :
    (replicate n a).erase b = replicate n a := by
  rw [erase_of_not_mem]
  simp_all

theorem Nodup.erase_eq_filter [LawfulBEq α] {l} (d : Nodup l) (a : α) : l.erase a = l.filter (· != a) := by
  induction d with
  | nil => rfl
  | cons m _n ih =>
    rename_i b l
    by_cases h : b = a
    · subst h
      rw [erase_cons_head, filter_cons_of_neg (by simp)]
      apply Eq.symm
      rw [filter_eq_self]
      simpa [@eq_comm α] using m
    · simp [beq_false_of_ne h, ih, h]

theorem Nodup.mem_erase_iff [LawfulBEq α] {a : α} (d : Nodup l) : a ∈ l.erase b ↔ a ≠ b ∧ a ∈ l := by
  rw [Nodup.erase_eq_filter d, mem_filter, and_comm, bne_iff_ne]

theorem Nodup.not_mem_erase [LawfulBEq α] {a : α} (h : Nodup l) : a ∉ l.erase a := fun H => by
  simpa using ((Nodup.mem_erase_iff h).mp H).left

theorem Nodup.erase [LawfulBEq α] (a : α) : Nodup l → Nodup (l.erase a) :=
  Nodup.sublist <| erase_sublist _ _

end erase

/-! ### eraseIdx -/

theorem length_eraseIdx : ∀ {l i}, i < length l → length (@eraseIdx α l i) = length l - 1
  | [], _, _ => rfl
  | _::_, 0, _ => by simp [eraseIdx]
  | x::xs, i+1, h => by
    have : i < length xs := Nat.lt_of_succ_lt_succ h
    simp [eraseIdx, ← Nat.add_one]
    rw [length_eraseIdx this, Nat.sub_add_cancel (Nat.lt_of_le_of_lt (Nat.zero_le _) this)]

@[simp] theorem eraseIdx_zero (l : List α) : eraseIdx l 0 = tail l := by cases l <;> rfl

theorem eraseIdx_eq_take_drop_succ :
    ∀ (l : List α) (i : Nat), l.eraseIdx i = l.take i ++ l.drop (i + 1)
  | nil, _ => by simp
  | a::l, 0 => by simp
  | a::l, i + 1 => by simp [eraseIdx_eq_take_drop_succ l i]

theorem eraseIdx_sublist : ∀ (l : List α) (k : Nat), eraseIdx l k <+ l
  | [], _ => by simp
  | a::l, 0 => by simp
  | a::l, k + 1 => by simp [eraseIdx_sublist l k]

theorem eraseIdx_subset (l : List α) (k : Nat) : eraseIdx l k ⊆ l := (eraseIdx_sublist l k).subset

@[simp]
theorem eraseIdx_eq_self : ∀ {l : List α} {k : Nat}, eraseIdx l k = l ↔ length l ≤ k
  | [], _ => by simp
  | a::l, 0 => by simp [(cons_ne_self _ _).symm]
  | a::l, k + 1 => by simp [eraseIdx_eq_self]

theorem eraseIdx_of_length_le {l : List α} {k : Nat} (h : length l ≤ k) : eraseIdx l k = l := by
  rw [eraseIdx_eq_self.2 h]

theorem eraseIdx_append_of_lt_length {l : List α} {k : Nat} (hk : k < length l) (l' : List α) :
    eraseIdx (l ++ l') k = eraseIdx l k ++ l' := by
  induction l generalizing k with
  | nil => simp_all
  | cons x l ih =>
    cases k with
    | zero => rfl
    | succ k => simp_all [eraseIdx_cons_succ, Nat.succ_lt_succ_iff]

theorem eraseIdx_append_of_length_le {l : List α} {k : Nat} (hk : length l ≤ k) (l' : List α) :
    eraseIdx (l ++ l') k = l ++ eraseIdx l' (k - length l) := by
  induction l generalizing k with
  | nil => simp_all
  | cons x l ih =>
    cases k with
    | zero => simp_all
    | succ k => simp_all [eraseIdx_cons_succ, Nat.succ_sub_succ]

protected theorem IsPrefix.eraseIdx {l l' : List α} (h : l <+: l') (k : Nat) :
    eraseIdx l k <+: eraseIdx l' k := by
  rcases h with ⟨t, rfl⟩
  if hkl : k < length l then
    simp [eraseIdx_append_of_lt_length hkl]
  else
    rw [Nat.not_lt] at hkl
    simp [eraseIdx_append_of_length_le hkl, eraseIdx_of_length_le hkl]

-- See also `mem_eraseIdx_iff_getElem` and `mem_eraseIdx_iff_getElem?` in
-- `Init/Data/List/Nat/Basic.lean`.

end List
