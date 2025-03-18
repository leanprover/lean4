/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro,
  Kim Morrison
-/
prelude
import Init.Data.List.TakeDrop

/-!
# Lemmas about `List.Subset`, `List.Sublist`, `List.IsPrefix`, `List.IsSuffix`, and `List.IsInfix`.
-/

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace List

open Nat

/-! ### isPrefixOf -/
section isPrefixOf
variable [BEq α]

@[simp] theorem isPrefixOf_cons₂_self [LawfulBEq α] {a : α} :
    isPrefixOf (a::as) (a::bs) = isPrefixOf as bs := by simp [isPrefixOf_cons₂]

@[simp] theorem isPrefixOf_length_pos_nil {l : List α} (h : 0 < l.length) : isPrefixOf l [] = false := by
  cases l <;> simp_all [isPrefixOf]

@[simp] theorem isPrefixOf_replicate {a : α} :
    isPrefixOf l (replicate n a) = (decide (l.length ≤ n) && l.all (· == a)) := by
  induction l generalizing n with
  | nil => simp
  | cons _ _ ih =>
    cases n
    · simp
    · simp [replicate_succ, isPrefixOf_cons₂, ih, Nat.succ_le_succ_iff, Bool.and_left_comm]

end isPrefixOf

/-! ### isSuffixOf -/
section isSuffixOf
variable [BEq α]

@[simp] theorem isSuffixOf_cons_nil : isSuffixOf (a::as) ([] : List α) = false := by
  simp [isSuffixOf]

@[simp] theorem isSuffixOf_replicate {a : α} :
    isSuffixOf l (replicate n a) = (decide (l.length ≤ n) && l.all (· == a)) := by
  simp [isSuffixOf, all_eq]

end isSuffixOf

/-! ### Subset -/

/-! ### List subset -/

theorem subset_def {l₁ l₂ : List α} : l₁ ⊆ l₂ ↔ ∀ {a : α}, a ∈ l₁ → a ∈ l₂ := .rfl

@[simp] theorem nil_subset (l : List α) : [] ⊆ l := nofun

@[simp] theorem Subset.refl (l : List α) : l ⊆ l := fun _ i => i

theorem Subset.trans {l₁ l₂ l₃ : List α} (h₁ : l₁ ⊆ l₂) (h₂ : l₂ ⊆ l₃) : l₁ ⊆ l₃ :=
  fun _ i => h₂ (h₁ i)

instance : Trans (fun l₁ l₂ => Subset l₂ l₁) (Membership.mem : List α → α → Prop) Membership.mem :=
  ⟨fun h₁ h₂ => h₁ h₂⟩

instance : Trans (Subset : List α → List α → Prop) Subset Subset :=
  ⟨Subset.trans⟩

theorem subset_cons_self (a : α) (l : List α) : l ⊆ a :: l := fun _ => Mem.tail _

theorem subset_of_cons_subset {a : α} {l₁ l₂ : List α} : a :: l₁ ⊆ l₂ → l₁ ⊆ l₂ :=
  fun s _ i => s (mem_cons_of_mem _ i)

@[simp] theorem subset_cons_of_subset (a : α) {l₁ l₂ : List α} : l₁ ⊆ l₂ → l₁ ⊆ a :: l₂ :=
  fun s _ i => .tail _ (s i)

theorem cons_subset_cons {l₁ l₂ : List α} (a : α) (s : l₁ ⊆ l₂) : a :: l₁ ⊆ a :: l₂ :=
  fun _ => by simp only [mem_cons]; exact Or.imp_right (@s _)

@[simp] theorem cons_subset : a :: l ⊆ m ↔ a ∈ m ∧ l ⊆ m := by
  simp only [subset_def, mem_cons, or_imp, forall_and, forall_eq]

@[simp] theorem subset_nil {l : List α} : l ⊆ [] ↔ l = [] :=
  ⟨fun h => match l with | [] => rfl | _::_ => (nomatch h (.head ..)), fun | rfl => Subset.refl _⟩

theorem eq_nil_of_subset_nil {l : List α} : l ⊆ [] → l = [] := subset_nil.mp

theorem map_subset {l₁ l₂ : List α} (f : α → β) (h : l₁ ⊆ l₂) : map f l₁ ⊆ map f l₂ :=
  fun x => by simp only [mem_map]; exact .imp fun a => .imp_left (@h _)

theorem filter_subset {l₁ l₂ : List α} (p : α → Bool) (H : l₁ ⊆ l₂) : filter p l₁ ⊆ filter p l₂ :=
  fun x => by simp_all [mem_filter, subset_def.1 H]

theorem filterMap_subset {l₁ l₂ : List α} (f : α → Option β) (H : l₁ ⊆ l₂) :
    filterMap f l₁ ⊆ filterMap f l₂ := by
  intro x
  simp only [mem_filterMap]
  rintro ⟨a, h, w⟩
  exact ⟨a, H h, w⟩

theorem subset_append_left (l₁ l₂ : List α) : l₁ ⊆ l₁ ++ l₂ := fun _ => mem_append_left _

theorem subset_append_right (l₁ l₂ : List α) : l₂ ⊆ l₁ ++ l₂ := fun _ => mem_append_right _

@[simp] theorem subset_append_of_subset_left (l₂ : List α) : l ⊆ l₁ → l ⊆ l₁ ++ l₂ :=
fun s => Subset.trans s <| subset_append_left _ _

@[simp] theorem subset_append_of_subset_right (l₁ : List α) : l ⊆ l₂ → l ⊆ l₁ ++ l₂ :=
fun s => Subset.trans s <| subset_append_right _ _

@[simp] theorem append_subset {l₁ l₂ l : List α} :
    l₁ ++ l₂ ⊆ l ↔ l₁ ⊆ l ∧ l₂ ⊆ l := by simp [subset_def, or_imp, forall_and]

theorem replicate_subset {n : Nat} {a : α} {l : List α} : replicate n a ⊆ l ↔ n = 0 ∨ a ∈ l := by
  induction n with
  | zero => simp
  | succ n ih => simp +contextual [replicate_succ, ih, cons_subset]

theorem subset_replicate {n : Nat} {a : α} {l : List α} (h : n ≠ 0) : l ⊆ replicate n a ↔ ∀ x ∈ l, x = a := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [cons_subset, mem_replicate, ne_eq, ih, mem_cons, forall_eq_or_imp,
      and_congr_left_iff, and_iff_right_iff_imp]
    solve_by_elim

@[simp] theorem reverse_subset {l₁ l₂ : List α} : reverse l₁ ⊆ l₂ ↔ l₁ ⊆ l₂ := by
  simp [subset_def]

@[simp] theorem subset_reverse {l₁ l₂ : List α} : l₁ ⊆ reverse l₂ ↔ l₁ ⊆ l₂ := by
  simp [subset_def]

/-! ### Sublist and isSublist -/

@[simp] theorem nil_sublist : ∀ l : List α, [] <+ l
  | [] => .slnil
  | a :: l => (nil_sublist l).cons a

@[simp] theorem Sublist.refl : ∀ l : List α, l <+ l
  | [] => .slnil
  | a :: l => (Sublist.refl l).cons₂ a

theorem Sublist.trans {l₁ l₂ l₃ : List α} (h₁ : l₁ <+ l₂) (h₂ : l₂ <+ l₃) : l₁ <+ l₃ := by
  induction h₂ generalizing l₁ with
  | slnil => exact h₁
  | cons _ _ IH => exact (IH h₁).cons _
  | @cons₂ l₂ _ a _ IH =>
    generalize e : a :: l₂ = l₂' at h₁
    match h₁ with
    | .slnil => apply nil_sublist
    | .cons a' h₁' => cases e; apply (IH h₁').cons
    | .cons₂ a' h₁' => cases e; apply (IH h₁').cons₂

instance : Trans (@Sublist α) Sublist Sublist := ⟨Sublist.trans⟩

attribute [simp] Sublist.cons

theorem sublist_cons_self (a : α) (l : List α) : l <+ a :: l := (Sublist.refl l).cons _

theorem sublist_of_cons_sublist : a :: l₁ <+ l₂ → l₁ <+ l₂ :=
  (sublist_cons_self a l₁).trans

@[simp]
theorem cons_sublist_cons : a :: l₁ <+ a :: l₂ ↔ l₁ <+ l₂ :=
  ⟨fun | .cons _ s => sublist_of_cons_sublist s | .cons₂ _ s => s, .cons₂ _⟩

theorem sublist_or_mem_of_sublist (h : l <+ l₁ ++ a :: l₂) : l <+ l₁ ++ l₂ ∨ a ∈ l := by
  induction l₁ generalizing l with
  | nil => match h with
    | .cons _ h => exact .inl h
    | .cons₂ _ h => exact .inr (.head ..)
  | cons b l₁ IH =>
    match h with
    | .cons _ h => exact (IH h).imp_left (Sublist.cons _)
    | .cons₂ _ h => exact (IH h).imp (Sublist.cons₂ _) (.tail _)

theorem Sublist.subset : l₁ <+ l₂ → l₁ ⊆ l₂
  | .slnil, _, h => h
  | .cons _ s, _, h => .tail _ (s.subset h)
  | .cons₂ .., _, .head .. => .head ..
  | .cons₂ _ s, _, .tail _ h => .tail _ (s.subset h)

protected theorem Sublist.mem (hx : a ∈ l₁) (hl : l₁ <+ l₂) : a ∈ l₂ :=
  hl.subset hx

theorem Sublist.head_mem (s : ys <+ xs) (h) : ys.head h ∈ xs :=
  s.mem (List.head_mem h)

theorem Sublist.getLast_mem (s : ys <+ xs) (h) : ys.getLast h ∈ xs :=
  s.mem (List.getLast_mem h)

instance : Trans (@Sublist α) Subset Subset :=
  ⟨fun h₁ h₂ => trans h₁.subset h₂⟩

instance : Trans Subset (@Sublist α) Subset :=
  ⟨fun h₁ h₂ => trans h₁ h₂.subset⟩

instance : Trans (fun l₁ l₂ => Sublist l₂ l₁) (Membership.mem : List α → α → Prop) Membership.mem :=
  ⟨fun h₁ h₂ => h₁.subset h₂⟩

theorem mem_of_cons_sublist {a : α} {l₁ l₂ : List α} (s : a :: l₁ <+ l₂) : a ∈ l₂ :=
  (cons_subset.1 s.subset).1

@[simp] theorem sublist_nil {l : List α} : l <+ [] ↔ l = [] :=
  ⟨fun s => subset_nil.1 s.subset, fun H => H ▸ Sublist.refl _⟩

theorem eq_nil_of_sublist_nil {l : List α} (s : l <+ []) : l = [] :=
  eq_nil_of_subset_nil <| s.subset

theorem Sublist.length_le : l₁ <+ l₂ → length l₁ ≤ length l₂
  | .slnil => Nat.le_refl 0
  | .cons _l s => le_succ_of_le (length_le s)
  | .cons₂ _ s => succ_le_succ (length_le s)

theorem Sublist.eq_of_length : l₁ <+ l₂ → length l₁ = length l₂ → l₁ = l₂
  | .slnil, _ => rfl
  | .cons a s, h => nomatch Nat.not_lt.2 s.length_le (h ▸ lt_succ_self _)
  | .cons₂ a s, h => by rw [s.eq_of_length (succ.inj h)]

theorem Sublist.eq_of_length_le (s : l₁ <+ l₂) (h : length l₂ ≤ length l₁) : l₁ = l₂ :=
  s.eq_of_length <| Nat.le_antisymm s.length_le h

theorem Sublist.length_eq (s : l₁ <+ l₂) : length l₁ = length l₂ ↔ l₁ = l₂ :=
  ⟨s.eq_of_length, congrArg _⟩

theorem tail_sublist : ∀ l : List α, tail l <+ l
  | [] => .slnil
  | a::l => sublist_cons_self a l

protected theorem Sublist.tail : ∀ {l₁ l₂ : List α}, l₁ <+ l₂ → tail l₁ <+ tail l₂
  | _, _, slnil => .slnil
  | _, _, Sublist.cons _ h => (tail_sublist _).trans h
  | _, _, Sublist.cons₂ _ h => h

theorem Sublist.of_cons_cons {l₁ l₂ : List α} {a b : α} (h : a :: l₁ <+ b :: l₂) : l₁ <+ l₂ :=
  h.tail

protected theorem Sublist.map (f : α → β) {l₁ l₂} (s : l₁ <+ l₂) : map f l₁ <+ map f l₂ := by
  induction s with
  | slnil => simp
  | cons a s ih =>
    simpa using cons (f a) ih
  | cons₂ a s ih =>
    simpa using cons₂ (f a) ih

protected theorem Sublist.filterMap (f : α → Option β) (s : l₁ <+ l₂) :
    filterMap f l₁ <+ filterMap f l₂ := by
  induction s <;> simp [filterMap_cons] <;> split <;> simp [*, cons, cons₂]

protected theorem Sublist.filter (p : α → Bool) {l₁ l₂} (s : l₁ <+ l₂) : filter p l₁ <+ filter p l₂ := by
  rw [← filterMap_eq_filter]; apply s.filterMap

theorem head_filter_mem (xs : List α) (p : α → Bool) (h) : (xs.filter p).head h ∈ xs :=
  (filter_sublist xs).head_mem h

theorem getLast_filter_mem (xs : List α) (p : α → Bool) (h) : (xs.filter p).getLast h ∈ xs :=
  (filter_sublist xs).getLast_mem h

theorem sublist_filterMap_iff {l₁ : List β} {f : α → Option β} :
    l₁ <+ l₂.filterMap f ↔ ∃ l', l' <+ l₂ ∧ l₁ = l'.filterMap f := by
  induction l₂ generalizing l₁ with
  | nil => simp
  | cons a l₂ ih =>
    simp only [filterMap_cons]
    split
    · simp only [ih]
      constructor
      · rintro ⟨l', h, rfl⟩
        exact ⟨l', Sublist.cons a h, rfl⟩
      · rintro ⟨l', h, rfl⟩
        cases h with
        | cons _ h =>
          exact ⟨l', h, rfl⟩
        | cons₂ _ h =>
          rename_i l'
          exact ⟨l', h, by simp_all⟩
    · constructor
      · intro w
        cases w with
        | cons _ h =>
          obtain ⟨l', s, rfl⟩ := ih.1 h
          exact ⟨l', Sublist.cons a s, rfl⟩
        | cons₂ _ h =>
          rename_i l'
          obtain ⟨l', s, rfl⟩ := ih.1 h
          refine ⟨a :: l', Sublist.cons₂ a s, ?_⟩
          rwa [filterMap_cons_some]
      · rintro ⟨l', h, rfl⟩
        replace h := h.filterMap f
        rwa [filterMap_cons_some] at h
        assumption

theorem sublist_map_iff {l₁ : List β} {f : α → β} :
    l₁ <+ l₂.map f ↔ ∃ l', l' <+ l₂ ∧ l₁ = l'.map f := by
  simp only [← filterMap_eq_map, sublist_filterMap_iff]

theorem sublist_filter_iff {l₁ : List α} {p : α → Bool} :
    l₁ <+ l₂.filter p ↔ ∃ l', l' <+ l₂ ∧ l₁ = l'.filter p := by
  simp only [← filterMap_eq_filter, sublist_filterMap_iff]

theorem sublist_append_left : ∀ l₁ l₂ : List α, l₁ <+ l₁ ++ l₂
  | [], _ => nil_sublist _
  | _ :: l₁, l₂ => (sublist_append_left l₁ l₂).cons₂ _

theorem sublist_append_right : ∀ l₁ l₂ : List α, l₂ <+ l₁ ++ l₂
  | [], _ => Sublist.refl _
  | _ :: l₁, l₂ => (sublist_append_right l₁ l₂).cons _

@[simp] theorem singleton_sublist {a : α} {l} : [a] <+ l ↔ a ∈ l := by
  refine ⟨fun h => h.subset (mem_singleton_self _), fun h => ?_⟩
  obtain ⟨_, _, rfl⟩ := append_of_mem h
  exact ((nil_sublist _).cons₂ _).trans (sublist_append_right ..)

@[simp] theorem sublist_append_of_sublist_left (s : l <+ l₁) : l <+ l₁ ++ l₂ :=
  s.trans <| sublist_append_left ..

@[simp] theorem sublist_append_of_sublist_right (s : l <+ l₂) : l <+ l₁ ++ l₂ :=
  s.trans <| sublist_append_right ..

@[simp] theorem append_sublist_append_left : ∀ l, l ++ l₁ <+ l ++ l₂ ↔ l₁ <+ l₂
  | [] => Iff.rfl
  | _ :: l => cons_sublist_cons.trans (append_sublist_append_left l)

theorem Sublist.append_left : l₁ <+ l₂ → ∀ l, l ++ l₁ <+ l ++ l₂ :=
  fun h l => (append_sublist_append_left l).mpr h

theorem Sublist.append_right : l₁ <+ l₂ → ∀ l, l₁ ++ l <+ l₂ ++ l
  | .slnil, _ => Sublist.refl _
  | .cons _ h, _ => (h.append_right _).cons _
  | .cons₂ _ h, _ => (h.append_right _).cons₂ _

theorem Sublist.append (hl : l₁ <+ l₂) (hr : r₁ <+ r₂) : l₁ ++ r₁ <+ l₂ ++ r₂ :=
  (hl.append_right _).trans ((append_sublist_append_left _).2 hr)

theorem sublist_cons_iff {a : α} {l l'} :
    l <+ a :: l' ↔ l <+ l' ∨ ∃ r, l = a :: r ∧ r <+ l' := by
  constructor
  · intro h
    cases h with
    | cons _ h => exact Or.inl h
    | cons₂ _ h => exact Or.inr ⟨_, rfl, h⟩
  · rintro (h | ⟨r, rfl, h⟩)
    · exact h.cons _
    · exact h.cons₂ _

theorem cons_sublist_iff {a : α} {l l'} :
    a :: l <+ l' ↔ ∃ r₁ r₂, l' = r₁ ++ r₂ ∧ a ∈ r₁ ∧ l <+ r₂ := by
  induction l' with
  | nil => simp
  | cons a' l' ih =>
    constructor
    · intro w
      cases w with
      | cons _ w =>
        obtain ⟨r₁, r₂, rfl, h₁, h₂⟩ := ih.1 w
        exact ⟨a' :: r₁, r₂, by simp, mem_cons_of_mem a' h₁, h₂⟩
      | cons₂ _ w =>
        exact ⟨[a], l', by simp, mem_singleton_self _, w⟩
    · rintro ⟨r₁, r₂, w, h₁, h₂⟩
      rw [w, ← singleton_append]
      exact Sublist.append (by simpa) h₂

theorem sublist_append_iff {l : List α} :
    l <+ r₁ ++ r₂ ↔ ∃ l₁ l₂, l = l₁ ++ l₂ ∧ l₁ <+ r₁ ∧ l₂ <+ r₂ := by
  induction r₁ generalizing l with
  | nil =>
    constructor
    · intro w
      refine ⟨[], l, by simp_all⟩
    · rintro ⟨l₁, l₂, rfl, w₁, w₂⟩
      simp_all
  | cons r r₁ ih =>
    constructor
    · intro w
      simp only [cons_append] at w
      cases w with
      | cons _ w =>
        obtain ⟨l₁, l₂, rfl, w₁, w₂⟩ := ih.1 w
        exact ⟨l₁, l₂, rfl, Sublist.cons r w₁, w₂⟩
      | cons₂ _ w =>
        rename_i l
        obtain ⟨l₁, l₂, rfl, w₁, w₂⟩ := ih.1 w
        refine ⟨r :: l₁, l₂, by simp, cons_sublist_cons.mpr w₁, w₂⟩
    · rintro ⟨l₁, l₂, rfl, w₁, w₂⟩
      cases w₁ with
      | cons _ w₁ =>
        exact Sublist.cons _ (Sublist.append w₁ w₂)
      | cons₂ _ w₁ =>
        rename_i l
        exact Sublist.cons₂ _ (Sublist.append w₁ w₂)

theorem append_sublist_iff {l₁ l₂ : List α} :
    l₁ ++ l₂ <+ r ↔ ∃ r₁ r₂, r = r₁ ++ r₂ ∧ l₁ <+ r₁ ∧ l₂ <+ r₂ := by
  induction l₁ generalizing r with
  | nil =>
    constructor
    · intro w
      refine ⟨[], r, by simp_all⟩
    · rintro ⟨r₁, r₂, rfl, -, w₂⟩
      simp only [nil_append]
      exact sublist_append_of_sublist_right w₂
  | cons a l₁ ih =>
    constructor
    · rw [cons_append, cons_sublist_iff]
      rintro ⟨r₁, r₂, rfl, h₁, h₂⟩
      obtain ⟨s₁, s₂, rfl, t₁, t₂⟩ := ih.1 h₂
      refine ⟨r₁ ++ s₁, s₂, by simp, ?_, t₂⟩
      rw [← singleton_append]
      exact Sublist.append (by simpa) t₁
    · rintro ⟨r₁, r₂, rfl, h₁, h₂⟩
      exact Sublist.append h₁ h₂

theorem Sublist.of_sublist_append_left (w : ∀ a, a ∈ l → a ∉ l₂) (h : l <+ l₁ ++ l₂) : l <+ l₁ := by
  rw [sublist_append_iff] at h
  obtain ⟨l₁', l₂', rfl, h₁, h₂⟩ := h
  have : l₂' = [] := by
    rw [eq_nil_iff_forall_not_mem]
    exact fun x m => w x (mem_append_right l₁' m) (h₂.mem m)
  simp_all

theorem Sublist.of_sublist_append_right (w : ∀ a, a ∈ l → a ∉ l₁) (h : l <+ l₁ ++ l₂) : l <+ l₂ := by
  rw [sublist_append_iff] at h
  obtain ⟨l₁', l₂', rfl, h₁, h₂⟩ := h
  have : l₁' = [] := by
    rw [eq_nil_iff_forall_not_mem]
    exact fun x m => w x (mem_append_left l₂' m) (h₁.mem m)
  simp_all

theorem Sublist.middle {l : List α} (h : l <+ l₁ ++ l₂) (a : α) : l <+ l₁ ++ a :: l₂ := by
  rw [sublist_append_iff] at h
  obtain ⟨l₁', l₂', rfl, h₁, h₂⟩ := h
  exact Sublist.append h₁ (h₂.cons a)

theorem Sublist.reverse : l₁ <+ l₂ → l₁.reverse <+ l₂.reverse
  | .slnil => Sublist.refl _
  | .cons _ h => by rw [reverse_cons]; exact sublist_append_of_sublist_left h.reverse
  | .cons₂ _ h => by rw [reverse_cons, reverse_cons]; exact h.reverse.append_right _

@[simp] theorem reverse_sublist : l₁.reverse <+ l₂.reverse ↔ l₁ <+ l₂ :=
  ⟨fun h => l₁.reverse_reverse ▸ l₂.reverse_reverse ▸ h.reverse, Sublist.reverse⟩

theorem sublist_reverse_iff : l₁ <+ l₂.reverse ↔ l₁.reverse <+ l₂ :=
  by rw [← reverse_sublist, reverse_reverse]

@[simp] theorem append_sublist_append_right (l) : l₁ ++ l <+ l₂ ++ l ↔ l₁ <+ l₂ :=
  ⟨fun h => by
    have := h.reverse
    simp only [reverse_append, append_sublist_append_left, reverse_sublist] at this
    exact this,
   fun h => h.append_right l⟩

@[simp] theorem replicate_sublist_replicate {m n} (a : α) :
    replicate m a <+ replicate n a ↔ m ≤ n := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := h.length_le; simp only [length_replicate] at this ⊢; exact this
  · induction h with
    | refl => apply Sublist.refl
    | step => simp [*, replicate, Sublist.cons]

theorem sublist_replicate_iff : l <+ replicate m a ↔ ∃ n, n ≤ m ∧ l = replicate n a := by
  induction l generalizing m with
  | nil =>
    simp only [nil_sublist, true_iff]
    exact ⟨0, zero_le m, by simp⟩
  | cons b l ih =>
    constructor
    · intro w
      cases m with
      | zero => simp at w
      | succ m =>
        simp [replicate_succ] at w
        cases w with
        | cons _ w =>
          obtain ⟨n, le, rfl⟩ := ih.1 (sublist_of_cons_sublist w)
          obtain rfl := (mem_replicate.1 (mem_of_cons_sublist w)).2
          exact ⟨n+1, Nat.add_le_add_right le 1, rfl⟩
        | cons₂ _ w =>
          obtain ⟨n, le, rfl⟩ := ih.1 w
          refine ⟨n+1, Nat.add_le_add_right le 1, by simp [replicate_succ]⟩
    · rintro ⟨n, le, w⟩
      rw [w]
      exact (replicate_sublist_replicate a).2 le

theorem sublist_flatten_of_mem {L : List (List α)} {l} (h : l ∈ L) : l <+ L.flatten := by
  induction L with
  | nil => cases h
  | cons l' L ih =>
    rcases mem_cons.1 h with (rfl | h)
    · simp [h]
    · simp [ih h, flatten_cons, sublist_append_of_sublist_right]

theorem sublist_flatten_iff {L : List (List α)} {l} :
    l <+ L.flatten ↔
      ∃ L' : List (List α), l = L'.flatten ∧ ∀ i (_ : i < L'.length), L'[i] <+ L[i]?.getD [] := by
  induction L generalizing l with
  | nil =>
    constructor
    · intro w
      simp only [flatten_nil, sublist_nil] at w
      subst w
      exact ⟨[], by simp, fun i x => by cases x⟩
    · rintro ⟨L', rfl, h⟩
      simp only [flatten_nil, sublist_nil, flatten_eq_nil_iff]
      simp only [getElem?_nil, Option.getD_none, sublist_nil] at h
      exact (forall_getElem (p := (· = []))).1 h
  | cons l' L ih =>
    simp only [flatten_cons, sublist_append_iff, ih]
    constructor
    · rintro ⟨l₁, l₂, rfl, s, L', rfl, h⟩
      refine ⟨l₁ :: L', by simp, ?_⟩
      intro i lt
      cases i <;> simp_all
    · rintro ⟨L', rfl, h⟩
      cases L' with
      | nil =>
        exact ⟨[], [], by simp, by simp, [], by simp, fun i x => by cases x⟩
      | cons l₁ L' =>
        exact ⟨l₁, L'.flatten, by simp, by simpa using h 0 (by simp), L', rfl,
          fun i lt => by simpa using h (i+1) (Nat.add_lt_add_right lt 1)⟩

theorem flatten_sublist_iff {L : List (List α)} {l} :
    L.flatten <+ l ↔
      ∃ L' : List (List α), l = L'.flatten ∧ ∀ i (_ : i < L.length), L[i] <+ L'[i]?.getD [] := by
  induction L generalizing l with
  | nil =>
    constructor
    · intro _
      exact ⟨[l], by simp, fun i x => by cases x⟩
    · rintro ⟨L', rfl, _⟩
      simp only [flatten_nil, nil_sublist]
  | cons l' L ih =>
    simp only [flatten_cons, append_sublist_iff, ih]
    constructor
    · rintro ⟨l₁, l₂, rfl, s, L', rfl, h⟩
      refine ⟨l₁ :: L', by simp, ?_⟩
      intro i lt
      cases i <;> simp_all
    · rintro ⟨L', rfl, h⟩
      cases L' with
      | nil =>
        exact ⟨[], [], by simp, by simpa using h 0 (by simp), [], by simp,
          fun i x => by simpa using h (i+1) (Nat.add_lt_add_right x 1)⟩
      | cons l₁ L' =>
        exact ⟨l₁, L'.flatten, by simp, by simpa using h 0 (by simp), L', rfl,
          fun i lt => by simpa using h (i+1) (Nat.add_lt_add_right lt 1)⟩

@[simp] theorem isSublist_iff_sublist [BEq α] [LawfulBEq α] {l₁ l₂ : List α} :
    l₁.isSublist l₂ ↔ l₁ <+ l₂ := by
  cases l₁ <;> cases l₂ <;> simp [isSublist]
  case cons.cons hd₁ tl₁ hd₂ tl₂ =>
    if h_eq : hd₁ = hd₂ then
      simp [h_eq, cons_sublist_cons, isSublist_iff_sublist]
    else
      simp only [beq_iff_eq, h_eq]
      constructor
      · intro h_sub
        apply Sublist.cons
        exact isSublist_iff_sublist.mp h_sub
      · intro h_sub
        cases h_sub
        case cons h_sub =>
          exact isSublist_iff_sublist.mpr h_sub
        case cons₂ =>
          contradiction

instance [DecidableEq α] (l₁ l₂ : List α) : Decidable (l₁ <+ l₂) :=
  decidable_of_iff (l₁.isSublist l₂) isSublist_iff_sublist

protected theorem Sublist.drop : ∀ {l₁ l₂ : List α}, l₁ <+ l₂ → ∀ i, l₁.drop i <+ l₂.drop i
  | _, _, h, 0 => h
  | _, _, h, i + 1 => by rw [← drop_tail, ← drop_tail]; exact h.tail.drop i

/-! ### IsPrefix / IsSuffix / IsInfix -/

@[simp] theorem prefix_append (l₁ l₂ : List α) : l₁ <+: l₁ ++ l₂ := ⟨l₂, rfl⟩

@[simp] theorem suffix_append (l₁ l₂ : List α) : l₂ <:+ l₁ ++ l₂ := ⟨l₁, rfl⟩

theorem infix_append (l₁ l₂ l₃ : List α) : l₂ <:+: l₁ ++ l₂ ++ l₃ := ⟨l₁, l₃, rfl⟩

@[simp] theorem infix_append' (l₁ l₂ l₃ : List α) : l₂ <:+: l₁ ++ (l₂ ++ l₃) := by
  rw [← List.append_assoc]; apply infix_append

theorem IsPrefix.isInfix : l₁ <+: l₂ → l₁ <:+: l₂ := fun ⟨t, h⟩ => ⟨[], t, h⟩

theorem IsSuffix.isInfix : l₁ <:+ l₂ → l₁ <:+: l₂ := fun ⟨t, h⟩ => ⟨t, [], by rw [h, append_nil]⟩

@[simp] theorem nil_prefix {l : List α} : [] <+: l := ⟨l, rfl⟩

@[simp] theorem nil_suffix {l : List α} : [] <:+ l := ⟨l, append_nil _⟩

@[simp] theorem nil_infix {l : List α} : [] <:+: l := nil_prefix.isInfix

theorem prefix_refl (l : List α) : l <+: l := ⟨[], append_nil _⟩
@[simp] theorem prefix_rfl {l : List α} : l <+: l := prefix_refl l

theorem suffix_refl (l : List α) : l <:+ l := ⟨[], rfl⟩
@[simp] theorem suffix_rfl {l : List α} : l <:+ l := suffix_refl l

theorem infix_refl (l : List α) : l <:+: l := prefix_rfl.isInfix
@[simp] theorem infix_rfl {l : List α} : l <:+: l := infix_refl l

@[simp] theorem suffix_cons (a : α) : ∀ l, l <:+ a :: l := suffix_append [a]

theorem infix_cons : l₁ <:+: l₂ → l₁ <:+: a :: l₂ := fun ⟨l₁', l₂', h⟩ => ⟨a :: l₁', l₂', h ▸ rfl⟩

theorem infix_concat : l₁ <:+: l₂ → l₁ <:+: concat l₂ a := fun ⟨l₁', l₂', h⟩ =>
  ⟨l₁', concat l₂' a, by simp [← h, concat_eq_append, append_assoc]⟩

theorem IsPrefix.trans : ∀ {l₁ l₂ l₃ : List α}, l₁ <+: l₂ → l₂ <+: l₃ → l₁ <+: l₃
  | _, _, _, ⟨r₁, rfl⟩, ⟨r₂, rfl⟩ => ⟨r₁ ++ r₂, (append_assoc _ _ _).symm⟩

theorem IsSuffix.trans : ∀ {l₁ l₂ l₃ : List α}, l₁ <:+ l₂ → l₂ <:+ l₃ → l₁ <:+ l₃
  | _, _, _, ⟨l₁, rfl⟩, ⟨l₂, rfl⟩ => ⟨l₂ ++ l₁, append_assoc _ _ _⟩

theorem IsInfix.trans : ∀ {l₁ l₂ l₃ : List α}, l₁ <:+: l₂ → l₂ <:+: l₃ → l₁ <:+: l₃
  | l, _, _, ⟨l₁, r₁, rfl⟩, ⟨l₂, r₂, rfl⟩ => ⟨l₂ ++ l₁, r₁ ++ r₂, by simp only [append_assoc]⟩

protected theorem IsInfix.sublist : l₁ <:+: l₂ → l₁ <+ l₂
  | ⟨_, _, h⟩ => h ▸ (sublist_append_right ..).trans (sublist_append_left ..)

protected theorem IsInfix.subset (hl : l₁ <:+: l₂) : l₁ ⊆ l₂ :=
  hl.sublist.subset

protected theorem IsPrefix.sublist (h : l₁ <+: l₂) : l₁ <+ l₂ :=
  h.isInfix.sublist

protected theorem IsPrefix.subset (hl : l₁ <+: l₂) : l₁ ⊆ l₂ :=
  hl.sublist.subset

protected theorem IsSuffix.sublist (h : l₁ <:+ l₂) : l₁ <+ l₂ :=
  h.isInfix.sublist

protected theorem IsSuffix.subset (hl : l₁ <:+ l₂) : l₁ ⊆ l₂ :=
  hl.sublist.subset

@[simp] theorem infix_nil : l <:+: [] ↔ l = [] := ⟨(sublist_nil.1 ·.sublist), (· ▸ infix_rfl)⟩

@[simp] theorem prefix_nil : l <+: [] ↔ l = [] := ⟨(sublist_nil.1 ·.sublist), (· ▸ prefix_rfl)⟩

@[simp] theorem suffix_nil : l <:+ [] ↔ l = [] := ⟨(sublist_nil.1 ·.sublist), (· ▸ suffix_rfl)⟩

theorem eq_nil_of_infix_nil (h : l <:+: []) : l = [] := infix_nil.mp h
theorem eq_nil_of_prefix_nil (h : l <+: []) : l = [] := prefix_nil.mp h
theorem eq_nil_of_suffix_nil (h : l <:+ []) : l = [] := suffix_nil.mp h

theorem IsPrefix.ne_nil {xs ys : List α} (h : xs <+: ys) (hx : xs ≠ []) : ys ≠ [] := by
  rintro rfl; exact hx <| List.prefix_nil.mp h

theorem IsSuffix.ne_nil {xs ys : List α} (h : xs <:+ ys) (hx : xs ≠ []) : ys ≠ [] := by
  rintro rfl; exact hx <| List.suffix_nil.mp h

theorem IsInfix.ne_nil {xs ys : List α} (h : xs <:+: ys) (hx : xs ≠ []) : ys ≠ [] := by
  rintro rfl; exact hx <| List.infix_nil.mp h

theorem IsInfix.length_le (h : l₁ <:+: l₂) : l₁.length ≤ l₂.length :=
  h.sublist.length_le

theorem IsPrefix.length_le (h : l₁ <+: l₂) : l₁.length ≤ l₂.length :=
  h.sublist.length_le

theorem IsSuffix.length_le (h : l₁ <:+ l₂) : l₁.length ≤ l₂.length :=
  h.sublist.length_le

theorem IsPrefix.getElem {xs ys : List α} (h : xs <+: ys) {i} (hi : i < xs.length) :
    xs[i] = ys[i]'(Nat.le_trans hi h.length_le) := by
  obtain ⟨_, rfl⟩ := h
  exact (List.getElem_append_left hi).symm

-- See `Init.Data.List.Nat.Sublist` for `IsSuffix.getElem`.

theorem IsPrefix.mem (hx : a ∈ l₁) (hl : l₁ <+: l₂) : a ∈ l₂ :=
  hl.subset hx

theorem IsSuffix.mem (hx : a ∈ l₁) (hl : l₁ <:+ l₂) : a ∈ l₂ :=
  hl.subset hx

theorem IsInfix.mem (hx : a ∈ l₁) (hl : l₁ <:+: l₂) : a ∈ l₂ :=
  hl.subset hx

@[simp] theorem reverse_suffix : reverse l₁ <:+ reverse l₂ ↔ l₁ <+: l₂ :=
  ⟨fun ⟨r, e⟩ => ⟨reverse r, by rw [← reverse_reverse l₁, ← reverse_append, e, reverse_reverse]⟩,
   fun ⟨r, e⟩ => ⟨reverse r, by rw [← reverse_append, e]⟩⟩

@[simp] theorem reverse_prefix : reverse l₁ <+: reverse l₂ ↔ l₁ <:+ l₂ := by
  rw [← reverse_suffix]; simp only [reverse_reverse]

@[simp] theorem reverse_infix : reverse l₁ <:+: reverse l₂ ↔ l₁ <:+: l₂ := by
  refine ⟨fun ⟨s, t, e⟩ => ⟨reverse t, reverse s, ?_⟩, fun ⟨s, t, e⟩ => ⟨reverse t, reverse s, ?_⟩⟩
  · rw [← reverse_reverse l₁, append_assoc, ← reverse_append, ← reverse_append, e,
      reverse_reverse]
  · rw [append_assoc, ← reverse_append, ← reverse_append, e]

theorem IsInfix.reverse : l₁ <:+: l₂ → reverse l₁ <:+: reverse l₂ :=
  reverse_infix.2

theorem IsSuffix.reverse : l₁ <:+ l₂ → reverse l₁ <+: reverse l₂ :=
  reverse_prefix.2

theorem IsPrefix.reverse : l₁ <+: l₂ → reverse l₁ <:+ reverse l₂ :=
  reverse_suffix.2

theorem IsPrefix.head {l₁ l₂ : List α} (h : l₁ <+: l₂) (hx : l₁ ≠ []) :
    l₁.head hx = l₂.head (h.ne_nil hx) := by
  cases l₁ <;> cases l₂ <;> simp only [head_cons, ne_eq, not_true_eq_false] at hx ⊢
  all_goals (obtain ⟨_, h⟩ := h; injection h)

theorem IsSuffix.getLast {l₁ l₂ : List α} (h : l₁ <:+ l₂) (hx : l₁ ≠ []) :
    l₁.getLast hx = l₂.getLast (h.ne_nil hx) := by
  rw [← head_reverse (by simpa), h.reverse.head,
    head_reverse (by rintro h; simp only [reverse_eq_nil_iff] at h; simp_all)]

theorem prefix_concat (a : α) (l) : l <+: concat l a := by simp

theorem infix_iff_prefix_suffix {l₁ l₂ : List α} : l₁ <:+: l₂ ↔ ∃ t, l₁ <+: t ∧ t <:+ l₂ :=
  ⟨fun ⟨_, t, e⟩ => ⟨l₁ ++ t, ⟨_, rfl⟩, e ▸ append_assoc .. ▸ ⟨_, rfl⟩⟩,
    fun ⟨_, ⟨t, rfl⟩, s, e⟩ => ⟨s, t, append_assoc .. ▸ e⟩⟩

theorem infix_iff_suffix_prefix {l₁ l₂ : List α} : l₁ <:+: l₂ ↔ ∃ t, l₁ <:+ t ∧ t <+: l₂ :=
  ⟨fun ⟨s, t, e⟩ => ⟨s ++ l₁, ⟨_, rfl⟩, ⟨t, e⟩⟩,
    fun ⟨_, ⟨s, rfl⟩, t, e⟩ => ⟨s, t, append_assoc .. ▸ e⟩⟩

theorem IsInfix.eq_of_length (h : l₁ <:+: l₂) : l₁.length = l₂.length → l₁ = l₂ :=
  h.sublist.eq_of_length

theorem IsInfix.eq_of_length_le (h : l₁ <:+: l₂) : l₂.length ≤ l₁.length → l₁ = l₂ :=
  h.sublist.eq_of_length_le

theorem IsPrefix.eq_of_length (h : l₁ <+: l₂) : l₁.length = l₂.length → l₁ = l₂ :=
  h.sublist.eq_of_length

theorem IsPrefix.eq_of_length_le (h : l₁ <+: l₂) : l₂.length ≤ l₁.length → l₁ = l₂ :=
  h.sublist.eq_of_length_le

theorem IsSuffix.eq_of_length (h : l₁ <:+ l₂) : l₁.length = l₂.length → l₁ = l₂ :=
  h.sublist.eq_of_length

theorem IsSuffix.eq_of_length_le (h : l₁ <:+ l₂) : l₂.length ≤ l₁.length → l₁ = l₂ :=
  h.sublist.eq_of_length_le

theorem prefix_of_prefix_length_le :
    ∀ {l₁ l₂ l₃ : List α}, l₁ <+: l₃ → l₂ <+: l₃ → length l₁ ≤ length l₂ → l₁ <+: l₂
  | [], _, _, _, _, _ => nil_prefix
  | _ :: _, b :: _, _, ⟨_, rfl⟩, ⟨_, e⟩, ll => by
    injection e with _ e'; subst b
    rcases prefix_of_prefix_length_le ⟨_, rfl⟩ ⟨_, e'⟩ (le_of_succ_le_succ ll) with ⟨r₃, rfl⟩
    exact ⟨r₃, rfl⟩

theorem prefix_or_prefix_of_prefix (h₁ : l₁ <+: l₃) (h₂ : l₂ <+: l₃) : l₁ <+: l₂ ∨ l₂ <+: l₁ :=
  (Nat.le_total (length l₁) (length l₂)).imp (prefix_of_prefix_length_le h₁ h₂)
    (prefix_of_prefix_length_le h₂ h₁)

theorem suffix_of_suffix_length_le
    (h₁ : l₁ <:+ l₃) (h₂ : l₂ <:+ l₃) (ll : length l₁ ≤ length l₂) : l₁ <:+ l₂ :=
  reverse_prefix.1 <|
    prefix_of_prefix_length_le (reverse_prefix.2 h₁) (reverse_prefix.2 h₂) (by simp [ll])

theorem suffix_or_suffix_of_suffix (h₁ : l₁ <:+ l₃) (h₂ : l₂ <:+ l₃) : l₁ <:+ l₂ ∨ l₂ <:+ l₁ :=
  (prefix_or_prefix_of_prefix (reverse_prefix.2 h₁) (reverse_prefix.2 h₂)).imp reverse_prefix.1
    reverse_prefix.1

theorem prefix_cons_iff : l₁ <+: a :: l₂ ↔ l₁ = [] ∨ ∃ t, l₁ = a :: t ∧ t <+: l₂ := by
  cases l₁ with
  | nil => simp
  | cons a' l₁ =>
    constructor
    · rintro ⟨t, h⟩
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inr ⟨l₁, rfl, prefix_append l₁ t⟩
    · rintro (h | ⟨t, w, ⟨s, h'⟩⟩)
      · simp [h]
      · simp only [w]
        refine ⟨s, by simp [h']⟩

@[simp] theorem cons_prefix_cons : a :: l₁ <+: b :: l₂ ↔ a = b ∧ l₁ <+: l₂ := by
  simp only [prefix_cons_iff, cons.injEq, false_or, List.cons_ne_nil]
  constructor
  · rintro ⟨t, ⟨rfl, rfl⟩, h⟩
    exact ⟨rfl, h⟩
  · rintro ⟨rfl, h⟩
    exact ⟨l₁, ⟨rfl, rfl⟩, h⟩

theorem suffix_cons_iff : l₁ <:+ a :: l₂ ↔ l₁ = a :: l₂ ∨ l₁ <:+ l₂ := by
  constructor
  · rintro ⟨⟨hd, tl⟩, hl₃⟩
    · exact Or.inl hl₃
    · simp only [cons_append] at hl₃
      injection hl₃ with _ hl₄
      exact Or.inr ⟨_, hl₄⟩
  · rintro (rfl | hl₁)
    · exact (a :: l₂).suffix_refl
    · exact hl₁.trans (l₂.suffix_cons _)

theorem infix_cons_iff : l₁ <:+: a :: l₂ ↔ l₁ <+: a :: l₂ ∨ l₁ <:+: l₂ := by
  constructor
  · rintro ⟨⟨hd, tl⟩, t, hl₃⟩
    · exact Or.inl ⟨t, hl₃⟩
    · simp only [cons_append] at hl₃
      injection hl₃ with _ hl₄
      exact Or.inr ⟨_, t, hl₄⟩
  · rintro (h | hl₁)
    · exact h.isInfix
    · exact infix_cons hl₁

theorem prefix_concat_iff {l₁ l₂ : List α} {a : α} :
    l₁ <+: l₂ ++ [a] ↔ l₁ = l₂ ++ [a] ∨ l₁ <+: l₂ := by
  simp only [← reverse_suffix, reverse_concat, suffix_cons_iff]
  simp only [concat_eq_append, ← reverse_concat, reverse_eq_iff, reverse_reverse]

theorem suffix_concat_iff {l₁ l₂ : List α} {a : α} :
    l₁ <:+ l₂ ++ [a] ↔ l₁ = [] ∨ ∃ t, l₁ = t ++ [a] ∧ t <:+ l₂ := by
  rw [← reverse_prefix, reverse_concat, prefix_cons_iff]
  simp only [reverse_eq_nil_iff]
  apply or_congr_right
  constructor
  · rintro ⟨t, w, h⟩
    exact ⟨t.reverse, by simpa using congrArg reverse w, by simpa using h.reverse⟩
  · rintro ⟨t, rfl, h⟩
    exact ⟨t.reverse, by simp, by simpa using h.reverse⟩

theorem infix_concat_iff {l₁ l₂ : List α} {a : α} :
    l₁ <:+: l₂ ++ [a] ↔ l₁ <:+ l₂ ++ [a] ∨ l₁ <:+: l₂ := by
  rw [← reverse_infix, reverse_concat, infix_cons_iff, reverse_infix,
    ← reverse_prefix, reverse_concat]

theorem isPrefix_iff : l₁ <+: l₂ ↔ ∀ i (h : i < l₁.length), l₂[i]? = some l₁[i] := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons a l₁ ih =>
    cases l₂ with
    | nil =>
      simpa using ⟨0, by simp⟩
    | cons b l₂ =>
      simp only [cons_append, cons_prefix_cons, ih]
      rw (occs := [2]) [← Nat.and_forall_add_one]
      simp [Nat.succ_lt_succ_iff, eq_comm]

theorem isPrefix_iff_getElem {l₁ l₂ : List α} :
    l₁ <+: l₂ ↔ ∃ (h : l₁.length ≤ l₂.length), ∀ i (hx : i < l₁.length),
      l₁[i] = l₂[i]'(Nat.lt_of_lt_of_le hx h) where
  mp h := ⟨h.length_le, fun _ h' ↦ h.getElem h'⟩
  mpr h := by
    obtain ⟨hl, h⟩ := h
    induction l₂ generalizing l₁ with
    | nil =>
      simpa using hl
    | cons _ _ tail_ih =>
      cases l₁ with
      | nil =>
        exact nil_prefix
      | cons _ _ =>
        simp only [length_cons, Nat.add_le_add_iff_right, Fin.getElem_fin] at hl h
        simp only [cons_prefix_cons]
        exact ⟨h 0 (zero_lt_succ _), tail_ih hl fun a ha ↦ h a.succ (succ_lt_succ ha)⟩

-- See `Init.Data.List.Nat.Sublist` for `isSuffix_iff` and `ifInfix_iff`.

theorem isPrefix_filterMap_iff {β} {f : α → Option β} {l₁ : List α} {l₂ : List β} :
    l₂ <+: filterMap f l₁ ↔ ∃ l, l <+: l₁ ∧ l₂ = filterMap f l := by
  simp only [IsPrefix, append_eq_filterMap_iff]
  constructor
  · rintro ⟨_, l₁, l₂, rfl, rfl, rfl⟩
    exact ⟨l₁, ⟨l₂, rfl⟩, rfl⟩
  · rintro ⟨l₁, ⟨l₂, rfl⟩, rfl⟩
    exact ⟨_, l₁, l₂, rfl, rfl, rfl⟩

theorem isSuffix_filterMap_iff {β} {f : α → Option β} {l₁ : List α} {l₂ : List β} :
    l₂ <:+ filterMap f l₁ ↔ ∃ l, l <:+ l₁ ∧ l₂ = filterMap f l := by
  simp only [IsSuffix, append_eq_filterMap_iff]
  constructor
  · rintro ⟨_, l₁, l₂, rfl, rfl, rfl⟩
    exact ⟨l₂, ⟨l₁, rfl⟩, rfl⟩
  · rintro ⟨l₁, ⟨l₂, rfl⟩, rfl⟩
    exact ⟨_, l₂, l₁, rfl, rfl, rfl⟩

theorem isInfix_filterMap_iff {β} {f : α → Option β} {l₁ : List α} {l₂ : List β} :
    l₂ <:+: filterMap f l₁ ↔ ∃ l, l <:+: l₁ ∧ l₂ = filterMap f l := by
  simp only [IsInfix, append_eq_filterMap_iff, filterMap_eq_append_iff]
  constructor
  · rintro ⟨_, _, _, l₁, rfl, ⟨⟨l₂, l₃, rfl, rfl, rfl⟩, rfl⟩⟩
    exact ⟨l₃, ⟨l₂, l₁, rfl⟩, rfl⟩
  · rintro ⟨l₃, ⟨l₂, l₁, rfl⟩, rfl⟩
    exact ⟨_, _, _, l₁, rfl, ⟨⟨l₂, l₃, rfl, rfl, rfl⟩, rfl⟩⟩

theorem isPrefix_filter_iff {p : α → Bool} {l₁ l₂ : List α} :
    l₂ <+: l₁.filter p ↔ ∃ l, l <+: l₁ ∧ l₂ = l.filter p := by
  rw [← filterMap_eq_filter, isPrefix_filterMap_iff]

theorem isSuffix_filter_iff {p : α → Bool} {l₁ l₂ : List α} :
    l₂ <:+ l₁.filter p ↔ ∃ l, l <:+ l₁ ∧ l₂ = l.filter p := by
  rw [← filterMap_eq_filter, isSuffix_filterMap_iff]

theorem isInfix_filter_iff {p : α → Bool} {l₁ l₂ : List α} :
    l₂ <:+: l₁.filter p ↔ ∃ l, l <:+: l₁ ∧ l₂ = l.filter p := by
  rw [← filterMap_eq_filter, isInfix_filterMap_iff]

theorem isPrefix_map_iff {β} {f : α → β} {l₁ : List α} {l₂ : List β} :
    l₂ <+: l₁.map f ↔ ∃ l, l <+: l₁ ∧ l₂ = l.map f := by
  rw [← filterMap_eq_map, isPrefix_filterMap_iff]

theorem isSuffix_map_iff {β} {f : α → β} {l₁ : List α} {l₂ : List β} :
    l₂ <:+ l₁.map f ↔ ∃ l, l <:+ l₁ ∧ l₂ = l.map f := by
  rw [← filterMap_eq_map, isSuffix_filterMap_iff]

theorem isInfix_map_iff {β} {f : α → β} {l₁ : List α} {l₂ : List β} :
    l₂ <:+: l₁.map f ↔ ∃ l, l <:+: l₁ ∧ l₂ = l.map f := by
  rw [← filterMap_eq_map, isInfix_filterMap_iff]

theorem isPrefix_replicate_iff {n} {a : α} {l : List α} :
    l <+: List.replicate n a ↔ l.length ≤ n ∧ l = List.replicate l.length a := by
  rw [IsPrefix]
  simp only [append_eq_replicate_iff]
  constructor
  · rintro ⟨_, rfl, _, _⟩
    exact ⟨le_add_right .., ‹_›⟩
  · rintro ⟨h, w⟩
    refine ⟨replicate (n - l.length) a, ?_, ?_⟩
    · simpa using add_sub_of_le h
    · simpa using w

theorem isSuffix_replicate_iff {n} {a : α} {l : List α} :
    l <:+ List.replicate n a ↔ l.length ≤ n ∧ l = List.replicate l.length a := by
  rw [← reverse_prefix, reverse_replicate, isPrefix_replicate_iff]
  simp [reverse_eq_iff]

theorem isInfix_replicate_iff {n} {a : α} {l : List α} :
    l <:+: List.replicate n a ↔ l.length ≤ n ∧ l = List.replicate l.length a := by
  rw [IsInfix]
  simp only [append_eq_replicate_iff, length_append]
  constructor
  · rintro ⟨_, _, rfl, ⟨-, _, _⟩, _⟩
    exact ⟨le_add_right_of_le (le_add_left ..), ‹_›⟩
  · rintro ⟨h, w⟩
    refine ⟨replicate (n - l.length) a, [], ?_, ?_⟩
    · simpa using Nat.sub_add_cancel h
    · simpa using w

theorem infix_of_mem_flatten : ∀ {L : List (List α)}, l ∈ L → l <:+: flatten L
  | l' :: _, h =>
    match h with
    | List.Mem.head .. => infix_append [] _ _
    | List.Mem.tail _ hlMemL =>
      IsInfix.trans (infix_of_mem_flatten hlMemL) <| (suffix_append _ _).isInfix

@[simp] theorem prefix_append_right_inj (l) : l ++ l₁ <+: l ++ l₂ ↔ l₁ <+: l₂ :=
  exists_congr fun r => by rw [append_assoc, append_right_inj]

theorem prefix_cons_inj (a) : a :: l₁ <+: a :: l₂ ↔ l₁ <+: l₂ :=
  prefix_append_right_inj [a]

theorem take_prefix (i) (l : List α) : take i l <+: l :=
  ⟨_, take_append_drop _ _⟩

theorem drop_suffix (i) (l : List α) : drop i l <:+ l :=
  ⟨_, take_append_drop _ _⟩

theorem take_sublist (i) (l : List α) : take i l <+ l :=
  (take_prefix i l).sublist

theorem drop_sublist (i) (l : List α) : drop i l <+ l :=
  (drop_suffix i l).sublist

theorem take_subset (i) (l : List α) : take i l ⊆ l :=
  (take_sublist i l).subset

theorem drop_subset (i) (l : List α) : drop i l ⊆ l :=
  (drop_sublist i l).subset

theorem mem_of_mem_take {l : List α} (h : a ∈ l.take i) : a ∈ l :=
  take_subset _ _ h

theorem mem_of_mem_drop {i} {l : List α} (h : a ∈ l.drop i) : a ∈ l :=
  drop_subset _ _ h

theorem drop_suffix_drop_left (l : List α) {i j : Nat} (h : i ≤ j) : drop j l <:+ drop i l := by
  rw [← Nat.sub_add_cancel h, Nat.add_comm, ← drop_drop]
  apply drop_suffix

-- See `Init.Data.List.Nat.TakeDrop` for `take_prefix_take_left`.

theorem drop_sublist_drop_left (l : List α) {i j : Nat} (h : i ≤ j) : drop j l <+ drop i l :=
  (drop_suffix_drop_left l h).sublist

theorem drop_subset_drop_left (l : List α) {i j : Nat} (h : i ≤ j) : drop j l ⊆ drop i l :=
  (drop_sublist_drop_left l h).subset

theorem takeWhile_prefix (p : α → Bool) : l.takeWhile p <+: l :=
  ⟨l.dropWhile p, takeWhile_append_dropWhile p l⟩

theorem dropWhile_suffix (p : α → Bool) : l.dropWhile p <:+ l :=
  ⟨l.takeWhile p, takeWhile_append_dropWhile p l⟩

theorem takeWhile_sublist (p : α → Bool) : l.takeWhile p <+ l :=
  (takeWhile_prefix p).sublist

theorem dropWhile_sublist (p : α → Bool) : l.dropWhile p <+ l :=
  (dropWhile_suffix p).sublist

theorem takeWhile_subset {l : List α} (p : α → Bool) : l.takeWhile p ⊆ l :=
  (takeWhile_sublist p).subset

theorem dropWhile_subset {l : List α} (p : α → Bool) : l.dropWhile p ⊆ l :=
  (dropWhile_sublist p).subset

theorem dropLast_prefix : ∀ l : List α, l.dropLast <+: l
  | [] => ⟨nil, by rw [dropLast, List.append_nil]⟩
  | a :: l => ⟨_, dropLast_concat_getLast (cons_ne_nil a l)⟩

theorem dropLast_sublist (l : List α) : l.dropLast <+ l :=
  (dropLast_prefix l).sublist

theorem dropLast_subset (l : List α) : l.dropLast ⊆ l :=
  (dropLast_sublist l).subset

theorem tail_suffix (l : List α) : tail l <:+ l := by rw [← drop_one]; apply drop_suffix

theorem IsPrefix.map {β} (f : α → β) ⦃l₁ l₂ : List α⦄ (h : l₁ <+: l₂) : l₁.map f <+: l₂.map f := by
  obtain ⟨r, rfl⟩ := h
  rw [map_append]; apply prefix_append

theorem IsSuffix.map {β} (f : α → β) ⦃l₁ l₂ : List α⦄ (h : l₁ <:+ l₂) : l₁.map f <:+ l₂.map f := by
  obtain ⟨r, rfl⟩ := h
  rw [map_append]; apply suffix_append

theorem IsInfix.map {β} (f : α → β) ⦃l₁ l₂ : List α⦄ (h : l₁ <:+: l₂) : l₁.map f <:+: l₂.map f := by
  obtain ⟨r₁, r₂, rfl⟩ := h
  rw [map_append, map_append]; apply infix_append

theorem IsPrefix.filter (p : α → Bool) ⦃l₁ l₂ : List α⦄ (h : l₁ <+: l₂) :
    l₁.filter p <+: l₂.filter p := by
  obtain ⟨xs, rfl⟩ := h
  rw [filter_append]; apply prefix_append

theorem IsSuffix.filter (p : α → Bool) ⦃l₁ l₂ : List α⦄ (h : l₁ <:+ l₂) :
    l₁.filter p <:+ l₂.filter p := by
  obtain ⟨xs, rfl⟩ := h
  rw [filter_append]; apply suffix_append

theorem IsInfix.filter (p : α → Bool) ⦃l₁ l₂ : List α⦄ (h : l₁ <:+: l₂) :
    l₁.filter p <:+: l₂.filter p := by
  obtain ⟨xs, ys, rfl⟩ := h
  rw [filter_append, filter_append]; apply infix_append _

theorem IsPrefix.filterMap {β} (f : α → Option β) ⦃l₁ l₂ : List α⦄ (h : l₁ <+: l₂) :
    filterMap f l₁ <+: filterMap f l₂ := by
  obtain ⟨xs, rfl⟩ := h
  rw [filterMap_append]; apply prefix_append

theorem IsSuffix.filterMap {β} (f : α → Option β) ⦃l₁ l₂ : List α⦄ (h : l₁ <:+ l₂) :
    filterMap f l₁ <:+ filterMap f l₂ := by
  obtain ⟨xs, rfl⟩ := h
  rw [filterMap_append]; apply suffix_append

theorem IsInfix.filterMap {β} (f : α → Option β) ⦃l₁ l₂ : List α⦄ (h : l₁ <:+: l₂) :
    filterMap f l₁ <:+: filterMap f l₂ := by
  obtain ⟨xs, ys, rfl⟩ := h
  rw [filterMap_append, filterMap_append]; apply infix_append

@[simp] theorem isPrefixOf_iff_prefix [BEq α] [LawfulBEq α] {l₁ l₂ : List α} :
    l₁.isPrefixOf l₂ ↔ l₁ <+: l₂ := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons a l₁ ih =>
    cases l₂ with
    | nil => simp
    | cons a' l₂ => simp [isPrefixOf, ih]

instance [DecidableEq α] (l₁ l₂ : List α) : Decidable (l₁ <+: l₂) :=
  decidable_of_iff (l₁.isPrefixOf l₂) isPrefixOf_iff_prefix

@[simp] theorem isSuffixOf_iff_suffix [BEq α] [LawfulBEq α] {l₁ l₂ : List α} :
    l₁.isSuffixOf l₂ ↔ l₁ <:+ l₂ := by
  simp [isSuffixOf]

instance [DecidableEq α] (l₁ l₂ : List α) : Decidable (l₁ <:+ l₂) :=
  decidable_of_iff (l₁.isSuffixOf l₂) isSuffixOf_iff_suffix

theorem prefix_iff_eq_append : l₁ <+: l₂ ↔ l₁ ++ drop (length l₁) l₂ = l₂ :=
  ⟨by rintro ⟨r, rfl⟩; rw [drop_left], fun e => ⟨_, e⟩⟩

theorem prefix_iff_eq_take : l₁ <+: l₂ ↔ l₁ = take (length l₁) l₂ :=
  ⟨fun h => append_cancel_right <| (prefix_iff_eq_append.1 h).trans (take_append_drop _ _).symm,
    fun e => e.symm ▸ take_prefix _ _⟩

-- See `Init.Data.List.Nat.Sublist` for `suffix_iff_eq_append`, `prefix_take_iff`, and `suffix_iff_eq_drop`.

/-! ### Deprecations -/

@[deprecated sublist_flatten_of_mem (since := "2024-10-14")] abbrev sublist_join_of_mem := @sublist_flatten_of_mem
@[deprecated sublist_flatten_iff (since := "2024-10-14")] abbrev sublist_join_iff := @sublist_flatten_iff
@[deprecated flatten_sublist_iff (since := "2024-10-14")] abbrev flatten_join_iff := @flatten_sublist_iff
@[deprecated infix_of_mem_flatten (since := "2024-10-14")] abbrev infix_of_mem_join := @infix_of_mem_flatten

end List
