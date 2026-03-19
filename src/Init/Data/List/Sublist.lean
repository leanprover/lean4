/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro,
  Kim Morrison
-/
module

prelude
public import Init.BinderPredicates
public import Init.Ext
public import Init.PropLemmas
import Init.Data.Bool
import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop
import Init.TacticsExtra

public section

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

@[simp, grind =] theorem isPrefixOf_cons_cons_self [LawfulBEq α] {a : α} :
    isPrefixOf (a::as) (a::bs) = isPrefixOf as bs := by simp [isPrefixOf_cons_cons]

@[deprecated isPrefixOf_cons_cons_self (since := "2026-02-26")]
theorem isPrefixOf_cons₂_self [LawfulBEq α] {a : α} :
    isPrefixOf (a::as) (a::bs) = isPrefixOf as bs := isPrefixOf_cons_cons_self

@[simp] theorem isPrefixOf_length_pos_nil {l : List α} (h : 0 < l.length) : isPrefixOf l [] = false := by
  cases l <;> simp_all [isPrefixOf]

@[simp, grind =] theorem isPrefixOf_replicate {a : α} :
    isPrefixOf l (replicate n a) = ((l.length ≤ n) && l.all (· == a)) := by
  induction l generalizing n with
  | nil => simp
  | cons _ _ ih =>
    cases n
    · simp
    · simp [replicate_succ, isPrefixOf_cons_cons, ih, Nat.succ_le_succ_iff, Bool.and_left_comm]

end isPrefixOf

/-! ### isSuffixOf -/
section isSuffixOf
variable [BEq α]

@[simp, grind =] theorem isSuffixOf_cons_nil : isSuffixOf (a::as) ([] : List α) = false := by
  simp [isSuffixOf]

@[simp, grind =] theorem isSuffixOf_replicate {a : α} :
    isSuffixOf l (replicate n a) = (decide (l.length ≤ n) && l.all (· == a)) := by
  simp [isSuffixOf, all_eq]

end isSuffixOf

/-! ### Subset -/

/-! ### List subset -/

-- For now we don't annotate lemmas about `Subset` for `grind`, but instead just unfold the definition.
@[grind =] theorem subset_def {l₁ l₂ : List α} : l₁ ⊆ l₂ ↔ ∀ {a : α}, a ∈ l₁ → a ∈ l₂ := .rfl

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

grind_pattern map_subset => l₁ ⊆ l₂, map f l₁ where
  l₂ =/= List.map _ _
grind_pattern map_subset => l₁ ⊆ l₂, map f l₂ where
  l₁ =/= List.map _ _

theorem filter_subset {l₁ l₂ : List α} (p : α → Bool) (H : l₁ ⊆ l₂) : filter p l₁ ⊆ filter p l₂ :=
  fun x => by simp_all [mem_filter, subset_def.1 H]

grind_pattern filter_subset => l₁ ⊆ l₂, filter p l₁ where
  l₂ =/= List.filter _ _
grind_pattern filter_subset => l₁ ⊆ l₂, filter p l₂ where
  l₁ =/= List.filter _ _

theorem filterMap_subset {l₁ l₂ : List α} (f : α → Option β) (H : l₁ ⊆ l₂) :
    filterMap f l₁ ⊆ filterMap f l₂ := by
  intro x
  simp only [mem_filterMap]
  rintro ⟨a, h, w⟩
  exact ⟨a, H h, w⟩

grind_pattern filterMap_subset => l₁ ⊆ l₂, filterMap f l₁ where
  l₂ =/= List.filterMap _ _
grind_pattern filterMap_subset => l₁ ⊆ l₂, filterMap f l₂ where
  l₁ =/= List.filterMap _ _

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

@[simp, grind ←] theorem nil_sublist : ∀ l : List α, [] <+ l
  | [] => .slnil
  | a :: l => (nil_sublist l).cons a

@[simp, grind ←] theorem Sublist.refl : ∀ l : List α, l <+ l
  | [] => .slnil
  | a :: l => (Sublist.refl l).cons_cons a

theorem Sublist.trans {l₁ l₂ l₃ : List α} (h₁ : l₁ <+ l₂) (h₂ : l₂ <+ l₃) : l₁ <+ l₃ := by
  induction h₂ generalizing l₁ with
  | slnil => exact h₁
  | cons _ _ IH => exact (IH h₁).cons _
  | @cons_cons l₂ _ a _ IH =>
    generalize e : a :: l₂ = l₂' at h₁
    match h₁ with
    | .slnil => apply nil_sublist
    | .cons a' h₁' => cases e; apply (IH h₁').cons
    | .cons_cons a' h₁' => cases e; apply (IH h₁').cons_cons

instance : Trans (@Sublist α) Sublist Sublist := ⟨Sublist.trans⟩

attribute [simp, grind ←] Sublist.cons

theorem sublist_cons_self (a : α) (l : List α) : l <+ a :: l := (Sublist.refl l).cons _

theorem sublist_of_cons_sublist : a :: l₁ <+ l₂ → l₁ <+ l₂ :=
  (sublist_cons_self a l₁).trans

@[simp, grind =]
theorem cons_sublist_cons : a :: l₁ <+ a :: l₂ ↔ l₁ <+ l₂ :=
  ⟨fun | .cons _ s => sublist_of_cons_sublist s | .cons_cons _ s => s, .cons_cons _⟩

theorem sublist_or_mem_of_sublist (h : l <+ l₁ ++ a :: l₂) : l <+ l₁ ++ l₂ ∨ a ∈ l := by
  induction l₁ generalizing l with
  | nil => match h with
    | .cons _ h => exact .inl h
    | .cons_cons _ h => exact .inr (.head ..)
  | cons b l₁ IH =>
    match h with
    | .cons _ h => exact (IH h).imp_left (Sublist.cons _)
    | .cons_cons _ h => exact (IH h).imp (Sublist.cons_cons _) (.tail _)

@[grind →] theorem Sublist.subset : l₁ <+ l₂ → l₁ ⊆ l₂
  | .slnil, _, h => h
  | .cons _ s, _, h => .tail _ (s.subset h)
  | .cons_cons .., _, .head .. => .head ..
  | .cons_cons _ s, _, .tail _ h => .tail _ (s.subset h)

protected theorem Sublist.mem (hx : a ∈ l₁) (hl : l₁ <+ l₂) : a ∈ l₂ :=
  hl.subset hx

theorem Sublist.head_mem (s : ys <+ xs) (h) : ys.head h ∈ xs :=
  s.mem (List.head_mem h)

grind_pattern Sublist.head_mem => ys <+ xs, ys.head h

theorem Sublist.getLast_mem (s : ys <+ xs) (h) : ys.getLast h ∈ xs :=
  s.mem (List.getLast_mem h)

grind_pattern Sublist.getLast_mem => ys <+ xs, ys.getLast h

instance : Trans (@Sublist α) Subset Subset :=
  ⟨fun h₁ h₂ => trans h₁.subset h₂⟩

instance : Trans Subset (@Sublist α) Subset :=
  ⟨fun h₁ h₂ => trans h₁ h₂.subset⟩

instance : Trans (fun l₁ l₂ => Sublist l₂ l₁) (Membership.mem : List α → α → Prop) Membership.mem :=
  ⟨fun h₁ h₂ => h₁.subset h₂⟩

theorem mem_of_cons_sublist {a : α} {l₁ l₂ : List α} (s : a :: l₁ <+ l₂) : a ∈ l₂ :=
  (cons_subset.1 s.subset).1

@[simp, grind =] theorem sublist_nil {l : List α} : l <+ [] ↔ l = [] :=
  ⟨fun s => subset_nil.1 s.subset, fun H => H ▸ Sublist.refl _⟩

theorem eq_nil_of_sublist_nil {l : List α} (s : l <+ []) : l = [] :=
  eq_nil_of_subset_nil <| s.subset

theorem Sublist.length_le : l₁ <+ l₂ → length l₁ ≤ length l₂
  | .slnil => Nat.le_refl 0
  | .cons _l s => le_succ_of_le (length_le s)
  | .cons_cons _ s => succ_le_succ (length_le s)

grind_pattern Sublist.length_le => l₁ <+ l₂, length l₁
grind_pattern Sublist.length_le => l₁ <+ l₂, length l₂

theorem Sublist.eq_of_length : l₁ <+ l₂ → length l₁ = length l₂ → l₁ = l₂
  | .slnil, _ => rfl
  | .cons a s, h => nomatch Nat.not_lt.2 s.length_le (h ▸ lt_succ_self _)
  | .cons_cons a s, h => by rw [s.eq_of_length (succ.inj h)]

theorem Sublist.eq_of_length_le (s : l₁ <+ l₂) (h : length l₂ ≤ length l₁) : l₁ = l₂ :=
  s.eq_of_length <| Nat.le_antisymm s.length_le h

-- Only activate `eq_of_length_le` if we're already thinking about lengths.
grind_pattern Sublist.eq_of_length_le => l₁ <+ l₂, length l₁, length l₂ where
  guard length l₂ ≤ length l₁

theorem Sublist.length_eq (s : l₁ <+ l₂) : length l₁ = length l₂ ↔ l₁ = l₂ :=
  ⟨s.eq_of_length, congrArg _⟩

theorem tail_sublist : ∀ l : List α, tail l <+ l
  | [] => .slnil
  | a::l => sublist_cons_self a l

grind_pattern tail_sublist => tail l <+ _

@[grind ←]
protected theorem Sublist.tail : ∀ {l₁ l₂ : List α}, l₁ <+ l₂ → tail l₁ <+ tail l₂
  | _, _, slnil => .slnil
  | _, _, Sublist.cons _ h => (tail_sublist _).trans h
  | _, _, Sublist.cons_cons _ h => h

@[grind →]
theorem Sublist.of_cons_cons {l₁ l₂ : List α} {a b : α} (h : a :: l₁ <+ b :: l₂) : l₁ <+ l₂ :=
  h.tail

@[grind ←]
protected theorem Sublist.map (f : α → β) {l₁ l₂} (s : l₁ <+ l₂) : map f l₁ <+ map f l₂ := by
  induction s with
  | slnil => simp
  | cons a s ih =>
    simpa using cons (f a) ih
  | cons_cons a s ih =>
    simpa using cons_cons (f a) ih

grind_pattern Sublist.map => l₁ <+ l₂, map f l₁
grind_pattern Sublist.map => l₁ <+ l₂, map f l₂

protected theorem Sublist.filterMap (f : α → Option β) (s : l₁ <+ l₂) :
    filterMap f l₁ <+ filterMap f l₂ := by
  induction s <;> simp [filterMap_cons] <;> split <;> simp [*, cons]

grind_pattern Sublist.filterMap => filterMap f l₁ <+ filterMap f l₂ where
  l₁ =/= List.filterMap _ _
  l₂ =/= List.filterMap _ _
grind_pattern Sublist.filterMap => l₁ <+ l₂, filterMap f l₁ where
  l₂ =/= List.filterMap _ _
grind_pattern Sublist.filterMap => l₁ <+ l₂, filterMap f l₂ where
  l₁ =/= List.filterMap _ _

protected theorem Sublist.filter (p : α → Bool) {l₁ l₂} (s : l₁ <+ l₂) : filter p l₁ <+ filter p l₂ := by
  rw [← filterMap_eq_filter]; apply s.filterMap

grind_pattern Sublist.filter => filter p l₁ <+ filter p l₂ where
  l₁ =/= List.filter _ _
  l₂ =/= List.filter _ _
grind_pattern Sublist.filter => l₁ <+ l₂, l₁.filter p where
  l₂ =/= List.filter _ _
grind_pattern Sublist.filter => l₁ <+ l₂, l₂.filter p where
  l₁ =/= List.filter _ _

theorem head_filter_mem (xs : List α) (p : α → Bool) (h) : (xs.filter p).head h ∈ xs :=
  filter_sublist.head_mem h

theorem getLast_filter_mem (xs : List α) (p : α → Bool) (h) : (xs.filter p).getLast h ∈ xs :=
  filter_sublist.getLast_mem h

@[grind =]
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
        | cons_cons _ h =>
          rename_i l'
          exact ⟨l', h, by simp_all⟩
    · constructor
      · intro w
        cases w with
        | cons _ h =>
          obtain ⟨l', s, rfl⟩ := ih.1 h
          exact ⟨l', Sublist.cons a s, rfl⟩
        | cons_cons _ h =>
          rename_i l'
          obtain ⟨l', s, rfl⟩ := ih.1 h
          refine ⟨a :: l', Sublist.cons_cons a s, ?_⟩
          rwa [filterMap_cons_some]
      · rintro ⟨l', h, rfl⟩
        replace h := h.filterMap f
        rwa [filterMap_cons_some] at h
        assumption

@[grind =]
theorem sublist_map_iff {l₁ : List β} {f : α → β} :
    l₁ <+ l₂.map f ↔ ∃ l', l' <+ l₂ ∧ l₁ = l'.map f := by
  simp only [← filterMap_eq_map, sublist_filterMap_iff]

@[grind =]
theorem sublist_filter_iff {l₁ : List α} {p : α → Bool} :
    l₁ <+ l₂.filter p ↔ ∃ l', l' <+ l₂ ∧ l₁ = l'.filter p := by
  simp only [← filterMap_eq_filter, sublist_filterMap_iff]

theorem sublist_append_left : ∀ l₁ l₂ : List α, l₁ <+ l₁ ++ l₂
  | [], _ => nil_sublist _
  | _ :: l₁, l₂ => (sublist_append_left l₁ l₂).cons_cons _

grind_pattern sublist_append_left => Sublist, l₁ ++ l₂

theorem sublist_append_right : ∀ l₁ l₂ : List α, l₂ <+ l₁ ++ l₂
  | [], _ => Sublist.refl _
  | _ :: l₁, l₂ => (sublist_append_right l₁ l₂).cons _

grind_pattern sublist_append_right => Sublist, l₁ ++ l₂

@[simp, grind =] theorem singleton_sublist {a : α} {l} : [a] <+ l ↔ a ∈ l := by
  refine ⟨fun h => h.subset (mem_singleton_self _), fun h => ?_⟩
  obtain ⟨_, _, rfl⟩ := append_of_mem h
  exact ((nil_sublist _).cons_cons _).trans (sublist_append_right ..)

@[simp] theorem sublist_append_of_sublist_left (s : l <+ l₁) : l <+ l₁ ++ l₂ :=
  s.trans <| sublist_append_left ..

grind_pattern sublist_append_of_sublist_left => l <+ l₁, l₁ ++ l₂

@[simp] theorem sublist_append_of_sublist_right (s : l <+ l₂) : l <+ l₁ ++ l₂ :=
  s.trans <| sublist_append_right ..

grind_pattern sublist_append_of_sublist_right => l <+ l₂, l₁ ++ l₂

@[simp, grind =] theorem append_sublist_append_left : ∀ l, l ++ l₁ <+ l ++ l₂ ↔ l₁ <+ l₂
  | [] => Iff.rfl
  | _ :: l => cons_sublist_cons.trans (append_sublist_append_left l)

theorem Sublist.append_left : l₁ <+ l₂ → ∀ l, l ++ l₁ <+ l ++ l₂ :=
  fun h l => (append_sublist_append_left l).mpr h

theorem Sublist.append_right : l₁ <+ l₂ → ∀ l, l₁ ++ l <+ l₂ ++ l
  | .slnil, _ => Sublist.refl _
  | .cons _ h, _ => (h.append_right _).cons _
  | .cons_cons _ h, _ => (h.append_right _).cons_cons _

theorem Sublist.append (hl : l₁ <+ l₂) (hr : r₁ <+ r₂) : l₁ ++ r₁ <+ l₂ ++ r₂ :=
  (hl.append_right _).trans ((append_sublist_append_left _).2 hr)

grind_pattern Sublist.append => l₁ <+ l₂, r₁ <+ r₂, l₁ ++ r₁, l₂ ++ r₂

@[grind =]
theorem sublist_cons_iff {a : α} {l l'} :
    l <+ a :: l' ↔ l <+ l' ∨ ∃ r, l = a :: r ∧ r <+ l' := by
  constructor
  · intro h
    cases h with
    | cons _ h => exact Or.inl h
    | cons_cons _ h => exact Or.inr ⟨_, rfl, h⟩
  · rintro (h | ⟨r, rfl, h⟩)
    · exact h.cons _
    · exact h.cons_cons _

@[grind =]
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
      | cons_cons _ w =>
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
      | cons_cons _ w =>
        rename_i l
        obtain ⟨l₁, l₂, rfl, w₁, w₂⟩ := ih.1 w
        refine ⟨r :: l₁, l₂, by simp, cons_sublist_cons.mpr w₁, w₂⟩
    · rintro ⟨l₁, l₂, rfl, w₁, w₂⟩
      cases w₁ with
      | cons _ w₁ =>
        exact Sublist.cons _ (Sublist.append w₁ w₂)
      | cons_cons _ w₁ =>
        rename_i l
        exact Sublist.cons_cons _ (Sublist.append w₁ w₂)

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

@[grind ←]
theorem Sublist.middle {l : List α} (h : l <+ l₁ ++ l₂) (a : α) : l <+ l₁ ++ a :: l₂ := by
  rw [sublist_append_iff] at h
  obtain ⟨l₁', l₂', rfl, h₁, h₂⟩ := h
  exact Sublist.append h₁ (h₂.cons a)

theorem Sublist.reverse : l₁ <+ l₂ → l₁.reverse <+ l₂.reverse
  | .slnil => Sublist.refl _
  | .cons _ h => by rw [reverse_cons]; exact sublist_append_of_sublist_left h.reverse
  | .cons_cons _ h => by rw [reverse_cons, reverse_cons]; exact h.reverse.append_right _

@[simp, grind =] theorem reverse_sublist : l₁.reverse <+ l₂.reverse ↔ l₁ <+ l₂ :=
  ⟨fun h => l₁.reverse_reverse ▸ l₂.reverse_reverse ▸ h.reverse, Sublist.reverse⟩

@[grind _=_]
theorem sublist_reverse_iff : l₁ <+ l₂.reverse ↔ l₁.reverse <+ l₂ :=
  by rw [← reverse_sublist, reverse_reverse]

@[simp, grind =] theorem append_sublist_append_right (l) : l₁ ++ l <+ l₂ ++ l ↔ l₁ <+ l₂ :=
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

@[grind =]
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
        | cons_cons _ w =>
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
    · simp
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
      exact (forall_mem_iff_forall_getElem (P := (· = []))).2 h
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

@[simp, grind =] theorem isSublist_iff_sublist [BEq α] [LawfulBEq α] {l₁ l₂ : List α} :
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
        case cons_cons =>
          contradiction

instance [DecidableEq α] (l₁ l₂ : List α) : Decidable (l₁ <+ l₂) :=
  decidable_of_iff (l₁.isSublist l₂) isSublist_iff_sublist

@[grind ←]
protected theorem Sublist.drop : ∀ {l₁ l₂ : List α}, l₁ <+ l₂ → ∀ i, l₁.drop i <+ l₂.drop i
  | _, _, h, 0 => h
  | _, _, h, i + 1 => by rw [← drop_tail, ← drop_tail]; exact h.tail.drop i

/-! ### IsPrefix / IsSuffix / IsInfix -/

@[simp] theorem prefix_append (l₁ l₂ : List α) : l₁ <+: l₁ ++ l₂ := ⟨l₂, rfl⟩

grind_pattern prefix_append => l₁ <+: l₁ ++ l₂

@[simp] theorem suffix_append (l₁ l₂ : List α) : l₂ <:+ l₁ ++ l₂ := ⟨l₁, rfl⟩

grind_pattern suffix_append => l₂ <:+ l₁ ++ l₂

theorem infix_append (l₁ l₂ l₃ : List α) : l₂ <:+: l₁ ++ l₂ ++ l₃ := ⟨l₁, l₃, rfl⟩

@[simp] theorem infix_append' (l₁ l₂ l₃ : List α) : l₂ <:+: l₁ ++ (l₂ ++ l₃) := by
  rw [← List.append_assoc]; apply infix_append

grind_pattern infix_append' => l₂ <:+: l₁ ++ (l₂ ++ l₃)

theorem infix_append_left : l₁ <:+: l₁ ++ l₂ := ⟨[], l₂, rfl⟩
theorem infix_append_right : l₂ <:+: l₁ ++ l₂ := ⟨l₁, [], by simp⟩

theorem IsPrefix.isInfix : l₁ <+: l₂ → l₁ <:+: l₂ := fun ⟨t, h⟩ => ⟨[], t, h⟩

grind_pattern IsPrefix.isInfix => l₁ <+: l₂, IsInfix

theorem IsSuffix.isInfix : l₁ <:+ l₂ → l₁ <:+: l₂ := fun ⟨t, h⟩ => ⟨t, [], by rw [h, append_nil]⟩

grind_pattern IsSuffix.isInfix => l₁ <:+ l₂, IsInfix

@[simp, grind ←] theorem nil_prefix {l : List α} : [] <+: l := ⟨l, rfl⟩

@[simp, grind ←] theorem nil_suffix {l : List α} : [] <:+ l := ⟨l, append_nil _⟩

@[simp, grind ←] theorem nil_infix {l : List α} : [] <:+: l := nil_prefix.isInfix

theorem prefix_refl (l : List α) : l <+: l := ⟨[], append_nil _⟩
@[simp, grind ←] theorem prefix_rfl {l : List α} : l <+: l := prefix_refl l

theorem suffix_refl (l : List α) : l <:+ l := ⟨[], rfl⟩
@[simp, grind ←] theorem suffix_rfl {l : List α} : l <:+ l := suffix_refl l

theorem infix_refl (l : List α) : l <:+: l := prefix_rfl.isInfix
@[simp, grind ←] theorem infix_rfl {l : List α} : l <:+: l := infix_refl l

@[simp] theorem suffix_cons (a : α) : ∀ l, l <:+ a :: l := suffix_append [a]

grind_pattern suffix_cons => _ <:+ a :: l

@[simp]
theorem suffix_cons_append {a : α} {l₁ l₂ : List α} : l₂ <:+ a :: (l₁ ++ l₂) := by
  rw [← List.cons_append]
  exact List.suffix_append (a :: l₁) l₂

theorem infix_cons : l₁ <:+: l₂ → l₁ <:+: a :: l₂ := fun ⟨l₁', l₂', h⟩ => ⟨a :: l₁', l₂', h ▸ rfl⟩

theorem infix_concat : l₁ <:+: l₂ → l₁ <:+: concat l₂ a := fun ⟨l₁', l₂', h⟩ =>
  ⟨l₁', concat l₂' a, by simp [← h, concat_eq_append, append_assoc]⟩

theorem IsPrefix.trans : ∀ {l₁ l₂ l₃ : List α}, l₁ <+: l₂ → l₂ <+: l₃ → l₁ <+: l₃
  | _, _, _, ⟨r₁, rfl⟩, ⟨r₂, rfl⟩ => ⟨r₁ ++ r₂, (append_assoc _ _ _).symm⟩

grind_pattern IsPrefix.trans => l₁ <+: l₂, l₂ <+: l₃

theorem IsSuffix.trans : ∀ {l₁ l₂ l₃ : List α}, l₁ <:+ l₂ → l₂ <:+ l₃ → l₁ <:+ l₃
  | _, _, _, ⟨l₁, rfl⟩, ⟨l₂, rfl⟩ => ⟨l₂ ++ l₁, append_assoc _ _ _⟩

grind_pattern IsSuffix.trans => l₁ <:+ l₂, l₂ <:+ l₃

theorem IsInfix.trans : ∀ {l₁ l₂ l₃ : List α}, l₁ <:+: l₂ → l₂ <:+: l₃ → l₁ <:+: l₃
  | l, _, _, ⟨l₁, r₁, rfl⟩, ⟨l₂, r₂, rfl⟩ => ⟨l₂ ++ l₁, r₁ ++ r₂, by simp only [append_assoc]⟩

grind_pattern IsInfix.trans => l₁ <:+: l₂, l₂ <:+: l₃

theorem prefix_append_of_prefix (h : l₁ <+: l₂) : l₁ <+: l₂ ++ l₃ :=
  h.trans (prefix_append l₂ l₃)

grind_pattern prefix_append_of_prefix => l₁ <+: l₂, l₂ ++ l₃

theorem suffix_append_of_suffix (h : l₁ <:+ l₃) : l₁ <:+ l₂ ++ l₃ :=
  h.trans (suffix_append l₂ l₃)

grind_pattern suffix_append_of_suffix => l₁ <:+ l₃, l₂ ++ l₃

theorem infix_append_of_infix_left (h : l₁ <:+: l₂) : l₁ <:+: l₂ ++ l₃ :=
  h.trans infix_append_left

grind_pattern infix_append_of_infix_left => l₁ <:+: l₂, l₂ ++ l₃

theorem infix_append_of_infix_right (h : l₁ <:+: l₃) : l₁ <:+: l₂ ++ l₃ :=
  h.trans infix_append_right

grind_pattern infix_append_of_infix_right => l₁ <:+: l₃, l₂ ++ l₃

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

@[simp, grind =] theorem infix_nil : l <:+: [] ↔ l = [] := ⟨(sublist_nil.1 ·.sublist), (· ▸ infix_rfl)⟩

@[simp, grind =] theorem prefix_nil : l <+: [] ↔ l = [] := ⟨(sublist_nil.1 ·.sublist), (· ▸ prefix_rfl)⟩

@[simp, grind =] theorem suffix_nil : l <:+ [] ↔ l = [] := ⟨(sublist_nil.1 ·.sublist), (· ▸ suffix_rfl)⟩

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

grind_pattern IsInfix.length_le => l₁ <:+: l₂, l₁.length
grind_pattern IsInfix.length_le => l₁ <:+: l₂, l₂.length

theorem IsPrefix.length_le (h : l₁ <+: l₂) : l₁.length ≤ l₂.length :=
  h.sublist.length_le

grind_pattern IsPrefix.length_le => l₁ <+: l₂, l₁.length
grind_pattern IsPrefix.length_le => l₁ <+: l₂, l₂.length

theorem IsSuffix.length_le (h : l₁ <:+ l₂) : l₁.length ≤ l₂.length :=
  h.sublist.length_le

grind_pattern IsSuffix.length_le => l₁ <:+ l₂, l₁.length
grind_pattern IsSuffix.length_le => l₁ <:+ l₂, l₂.length

theorem IsPrefix.getElem {xs ys : List α} (h : xs <+: ys) {i} (hi : i < xs.length) :
    xs[i] = ys[i]'(Nat.le_trans hi h.length_le) := by
  obtain ⟨_, rfl⟩ := h
  exact (List.getElem_append_left hi).symm

-- See `Init.Data.List.Nat.Sublist` for `IsSuffix.getElem`.

@[grind →] theorem IsPrefix.mem (hx : a ∈ l₁) (hl : l₁ <+: l₂) : a ∈ l₂ :=
  hl.subset hx

@[grind →] theorem IsSuffix.mem (hx : a ∈ l₁) (hl : l₁ <:+ l₂) : a ∈ l₂ :=
  hl.subset hx

@[grind →] theorem IsInfix.mem (hx : a ∈ l₁) (hl : l₁ <:+: l₂) : a ∈ l₂ :=
  hl.subset hx

@[simp, grind =] theorem reverse_suffix : reverse l₁ <:+ reverse l₂ ↔ l₁ <+: l₂ :=
  ⟨fun ⟨r, e⟩ => ⟨reverse r, by rw [← reverse_reverse l₁, ← reverse_append, e, reverse_reverse]⟩,
   fun ⟨r, e⟩ => ⟨reverse r, by rw [← reverse_append, e]⟩⟩

@[simp, grind =] theorem reverse_prefix : reverse l₁ <+: reverse l₂ ↔ l₁ <:+ l₂ := by
  rw [← reverse_suffix]; simp only [reverse_reverse]

@[simp, grind =] theorem reverse_infix : reverse l₁ <:+: reverse l₂ ↔ l₁ <:+: l₂ := by
  refine ⟨fun ⟨s, t, e⟩ => ⟨reverse t, reverse s, ?_⟩, fun ⟨s, t, e⟩ => ⟨reverse t, reverse s, ?_⟩⟩
  · rw [← reverse_reverse l₁, append_assoc, ← reverse_append, ← reverse_append, e,
      reverse_reverse]
  · rw [append_assoc, ← reverse_append, ← reverse_append, e]

theorem IsInfix.reverse : l₁ <:+: l₂ → reverse l₁ <:+: reverse l₂ :=
  reverse_infix.2

grind_pattern IsInfix.reverse => l₁ <:+: l₂, l₁.reverse
grind_pattern IsInfix.reverse => l₁ <:+: l₂, l₂.reverse

theorem IsSuffix.reverse : l₁ <:+ l₂ → reverse l₁ <+: reverse l₂ :=
  reverse_prefix.2

grind_pattern IsSuffix.reverse => l₁ <:+ l₂, l₁.reverse
grind_pattern IsSuffix.reverse => l₁ <:+ l₂, l₂.reverse

theorem IsPrefix.reverse : l₁ <+: l₂ → reverse l₁ <:+ reverse l₂ :=
  reverse_suffix.2

grind_pattern IsPrefix.reverse => l₁ <+: l₂, l₁.reverse
grind_pattern IsPrefix.reverse => l₁ <+: l₂, l₂.reverse

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

@[simp, grind =] theorem cons_prefix_cons : a :: l₁ <+: b :: l₂ ↔ a = b ∧ l₁ <+: l₂ := by
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
  simp only [← reverse_concat, reverse_eq_iff, reverse_reverse]

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

theorem prefix_iff_getElem? {l₁ l₂ : List α} :
    l₁ <+: l₂ ↔ ∀ i (h : i < l₁.length), l₂[i]? = some l₁[i] := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons a l₁ ih =>
    cases l₂ with
    | nil =>
      simpa using ⟨0, by simp⟩
    | cons b l₂ =>
      simp only [cons_prefix_cons, ih]
      rw (occs := [2]) [← Nat.and_forall_add_one]
      simp [Nat.succ_lt_succ_iff, eq_comm]

-- See `Init.Data.List.Nat.Sublist` for `isSuffix_iff` and `ifInfix_iff`.

theorem prefix_iff_getElem {l₁ l₂ : List α} :
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
        simp only [length_cons, Nat.add_le_add_iff_right] at hl h
        simp only [cons_prefix_cons]
        exact ⟨h 0 (zero_lt_succ _), tail_ih hl fun a ha ↦ h a.succ (succ_lt_succ ha)⟩

theorem cons_prefix_iff {a : α} {l₁ l₂ : List α} :
    a :: l₁ <+: l₂ ↔ ∃ l', l₂ = a :: l' ∧ l₁ <+: l' := by
  match l₂ with
  | nil => simp
  | cons b l₂ => simp [and_assoc, eq_comm]

theorem prefix_filterMap_iff {β} {f : α → Option β} {l₁ : List α} {l₂ : List β} :
    l₂ <+: filterMap f l₁ ↔ ∃ l, l <+: l₁ ∧ l₂ = filterMap f l := by
  simp only [IsPrefix, append_eq_filterMap_iff]
  constructor
  · rintro ⟨_, l₁, l₂, rfl, rfl, rfl⟩
    exact ⟨l₁, ⟨l₂, rfl⟩, rfl⟩
  · rintro ⟨l₁, ⟨l₂, rfl⟩, rfl⟩
    exact ⟨_, l₁, l₂, rfl, rfl, rfl⟩

theorem suffix_filterMap_iff {β} {f : α → Option β} {l₁ : List α} {l₂ : List β} :
    l₂ <:+ filterMap f l₁ ↔ ∃ l, l <:+ l₁ ∧ l₂ = filterMap f l := by
  simp only [IsSuffix, append_eq_filterMap_iff]
  constructor
  · rintro ⟨_, l₁, l₂, rfl, rfl, rfl⟩
    exact ⟨l₂, ⟨l₁, rfl⟩, rfl⟩
  · rintro ⟨l₁, ⟨l₂, rfl⟩, rfl⟩
    exact ⟨_, l₂, l₁, rfl, rfl, rfl⟩

theorem infix_filterMap_iff {β} {f : α → Option β} {l₁ : List α} {l₂ : List β} :
    l₂ <:+: filterMap f l₁ ↔ ∃ l, l <:+: l₁ ∧ l₂ = filterMap f l := by
  simp only [IsInfix, append_eq_filterMap_iff, filterMap_eq_append_iff]
  constructor
  · rintro ⟨_, _, _, l₁, rfl, ⟨⟨l₂, l₃, rfl, rfl, rfl⟩, rfl⟩⟩
    exact ⟨l₃, ⟨l₂, l₁, rfl⟩, rfl⟩
  · rintro ⟨l₃, ⟨l₂, l₁, rfl⟩, rfl⟩
    exact ⟨_, _, _, l₁, rfl, ⟨⟨l₂, l₃, rfl, rfl, rfl⟩, rfl⟩⟩

theorem prefix_filter_iff {p : α → Bool} {l₁ l₂ : List α} :
    l₂ <+: l₁.filter p ↔ ∃ l, l <+: l₁ ∧ l₂ = l.filter p := by
  rw [← filterMap_eq_filter, prefix_filterMap_iff]

theorem suffix_filter_iff {p : α → Bool} {l₁ l₂ : List α} :
    l₂ <:+ l₁.filter p ↔ ∃ l, l <:+ l₁ ∧ l₂ = l.filter p := by
  rw [← filterMap_eq_filter, suffix_filterMap_iff]

theorem infix_filter_iff {p : α → Bool} {l₁ l₂ : List α} :
    l₂ <:+: l₁.filter p ↔ ∃ l, l <:+: l₁ ∧ l₂ = l.filter p := by
  rw [← filterMap_eq_filter, infix_filterMap_iff]

theorem prefix_map_iff {β} {f : α → β} {l₁ : List α} {l₂ : List β} :
    l₂ <+: l₁.map f ↔ ∃ l, l <+: l₁ ∧ l₂ = l.map f := by
  rw [← filterMap_eq_map, prefix_filterMap_iff]

theorem suffix_map_iff {β} {f : α → β} {l₁ : List α} {l₂ : List β} :
    l₂ <:+ l₁.map f ↔ ∃ l, l <:+ l₁ ∧ l₂ = l.map f := by
  rw [← filterMap_eq_map, suffix_filterMap_iff]

theorem infix_map_iff {β} {f : α → β} {l₁ : List α} {l₂ : List β} :
    l₂ <:+: l₁.map f ↔ ∃ l, l <:+: l₁ ∧ l₂ = l.map f := by
  rw [← filterMap_eq_map, infix_filterMap_iff]

@[grind =] theorem prefix_replicate_iff {n} {a : α} {l : List α} :
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

@[grind =] theorem suffix_replicate_iff {n} {a : α} {l : List α} :
    l <:+ List.replicate n a ↔ l.length ≤ n ∧ l = List.replicate l.length a := by
  rw [← reverse_prefix, reverse_replicate, prefix_replicate_iff]
  simp [reverse_eq_iff]

@[grind =] theorem infix_replicate_iff {n} {a : α} {l : List α} :
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

grind_pattern take_prefix => take i l <+: _

theorem drop_suffix (i) (l : List α) : drop i l <:+ l :=
  ⟨_, take_append_drop _ _⟩

grind_pattern drop_suffix => drop i l <+: _

theorem take_sublist (i) (l : List α) : take i l <+ l :=
  (take_prefix i l).sublist

grind_pattern take_sublist => take i l <+ l

theorem drop_sublist (i) (l : List α) : drop i l <+ l :=
  (drop_suffix i l).sublist

grind_pattern drop_sublist => drop i l <+ l

theorem take_subset (i) (l : List α) : take i l ⊆ l :=
  (take_sublist i l).subset

grind_pattern take_subset => take i l ⊆ l

theorem drop_subset (i) (l : List α) : drop i l ⊆ l :=
  (drop_sublist i l).subset

grind_pattern drop_subset => drop i l ⊆ l

@[grind →]
theorem mem_of_mem_take {l : List α} (h : a ∈ l.take i) : a ∈ l :=
  take_subset _ _ h

@[grind →]
theorem mem_of_mem_drop {i} {l : List α} (h : a ∈ l.drop i) : a ∈ l :=
  drop_subset _ _ h

theorem drop_suffix_drop_left (l : List α) {i j : Nat} (h : i ≤ j) : drop j l <:+ drop i l := by
  rw [← Nat.sub_add_cancel h, Nat.add_comm, ← drop_drop]
  apply drop_suffix

-- See `Init.Data.List.Nat.TakeDrop` for `take_prefix_take_left`.

@[grind ←] theorem drop_sublist_drop_left (l : List α) {i j : Nat} (h : i ≤ j) : drop j l <+ drop i l :=
  (drop_suffix_drop_left l h).sublist

@[grind ←] theorem drop_subset_drop_left (l : List α) {i j : Nat} (h : i ≤ j) : drop j l ⊆ drop i l :=
  (drop_sublist_drop_left l h).subset

theorem takeWhile_prefix (p : α → Bool) : l.takeWhile p <+: l :=
  ⟨l.dropWhile p, takeWhile_append_dropWhile⟩

grind_pattern takeWhile_prefix => l.takeWhile p <+: _

theorem dropWhile_suffix (p : α → Bool) : l.dropWhile p <:+ l :=
  ⟨l.takeWhile p, takeWhile_append_dropWhile⟩

grind_pattern dropWhile_suffix => l.dropWhile p <+: _

theorem takeWhile_sublist (p : α → Bool) : l.takeWhile p <+ l :=
  (takeWhile_prefix p).sublist

grind_pattern takeWhile_sublist => l.takeWhile p <+ _

theorem dropWhile_sublist (p : α → Bool) : l.dropWhile p <+ l :=
  (dropWhile_suffix p).sublist

grind_pattern dropWhile_sublist => l.dropWhile p <+ _

theorem takeWhile_subset {l : List α} (p : α → Bool) : l.takeWhile p ⊆ l :=
  (takeWhile_sublist p).subset

grind_pattern takeWhile_subset => l.takeWhile p ⊆ _

theorem dropWhile_subset {l : List α} (p : α → Bool) : l.dropWhile p ⊆ l :=
  (dropWhile_sublist p).subset

grind_pattern dropWhile_subset => l.dropWhile p ⊆ _

theorem dropLast_prefix : ∀ l : List α, l.dropLast <+: l
  | [] => ⟨nil, by rw [dropLast, List.append_nil]⟩
  | a :: l => ⟨_, dropLast_concat_getLast (cons_ne_nil a l)⟩

grind_pattern dropLast_prefix => l.dropLast <+: _

theorem dropLast_sublist (l : List α) : l.dropLast <+ l :=
  (dropLast_prefix l).sublist

grind_pattern dropLast_sublist => l.dropLast <+ _

theorem dropLast_subset (l : List α) : l.dropLast ⊆ l :=
  (dropLast_sublist l).subset

grind_pattern dropLast_subset => l.dropLast ⊆ _

theorem tail_suffix (l : List α) : tail l <:+ l := by rw [← drop_one]; apply drop_suffix

grind_pattern tail_suffix => tail l <+: _

@[grind ←] theorem IsPrefix.map {β} (f : α → β) ⦃l₁ l₂ : List α⦄ (h : l₁ <+: l₂) : l₁.map f <+: l₂.map f := by
  obtain ⟨r, rfl⟩ := h
  rw [map_append]; apply prefix_append

grind_pattern IsPrefix.map => l₁ <+: l₂, l₁.map f
grind_pattern IsPrefix.map => l₁ <+: l₂, l₂.map f

@[grind ←] theorem IsSuffix.map {β} (f : α → β) ⦃l₁ l₂ : List α⦄ (h : l₁ <:+ l₂) : l₁.map f <:+ l₂.map f := by
  obtain ⟨r, rfl⟩ := h
  rw [map_append]; apply suffix_append

grind_pattern IsSuffix.map => l₁ <:+ l₂, l₁.map f
grind_pattern IsSuffix.map => l₁ <:+ l₂, l₂.map f

@[grind ←] theorem IsInfix.map {β} (f : α → β) ⦃l₁ l₂ : List α⦄ (h : l₁ <:+: l₂) : l₁.map f <:+: l₂.map f := by
  obtain ⟨r₁, r₂, rfl⟩ := h
  rw [map_append, map_append]; apply infix_append

grind_pattern IsInfix.map => l₁ <:+: l₂, l₁.map f
grind_pattern IsInfix.map => l₁ <:+: l₂, l₂.map f

@[grind ←] theorem IsPrefix.filter (p : α → Bool) ⦃l₁ l₂ : List α⦄ (h : l₁ <+: l₂) :
    l₁.filter p <+: l₂.filter p := by
  obtain ⟨xs, rfl⟩ := h
  rw [filter_append]; apply prefix_append

grind_pattern IsPrefix.filter => l₁ <+: l₂, l₁.filter p
grind_pattern IsPrefix.filter => l₁ <+: l₂, l₂.filter p

@[grind ←] theorem IsSuffix.filter (p : α → Bool) ⦃l₁ l₂ : List α⦄ (h : l₁ <:+ l₂) :
    l₁.filter p <:+ l₂.filter p := by
  obtain ⟨xs, rfl⟩ := h
  rw [filter_append]; apply suffix_append

grind_pattern IsSuffix.filter => l₁ <:+ l₂, l₁.filter p
grind_pattern IsSuffix.filter => l₁ <:+ l₂, l₂.filter p

@[grind ←] theorem IsInfix.filter (p : α → Bool) ⦃l₁ l₂ : List α⦄ (h : l₁ <:+: l₂) :
    l₁.filter p <:+: l₂.filter p := by
  obtain ⟨xs, ys, rfl⟩ := h
  rw [filter_append, filter_append]; apply infix_append _

grind_pattern IsInfix.filter => l₁ <:+: l₂, l₁.filter p
grind_pattern IsInfix.filter => l₁ <:+: l₂, l₂.filter p

@[grind ←] theorem IsPrefix.filterMap {β} (f : α → Option β) ⦃l₁ l₂ : List α⦄ (h : l₁ <+: l₂) :
    filterMap f l₁ <+: filterMap f l₂ := by
  obtain ⟨xs, rfl⟩ := h
  rw [filterMap_append]; apply prefix_append

grind_pattern IsPrefix.filterMap => l₁ <+: l₂, filterMap f l₁
grind_pattern IsPrefix.filterMap => l₁ <+: l₂, filterMap f l₂

@[grind ←] theorem IsSuffix.filterMap {β} (f : α → Option β) ⦃l₁ l₂ : List α⦄ (h : l₁ <:+ l₂) :
    filterMap f l₁ <:+ filterMap f l₂ := by
  obtain ⟨xs, rfl⟩ := h
  rw [filterMap_append]; apply suffix_append

grind_pattern IsSuffix.filterMap => l₁ <:+ l₂, filterMap f l₁
grind_pattern IsSuffix.filterMap => l₁ <:+ l₂, filterMap f l₂

@[grind ←] theorem IsInfix.filterMap {β} (f : α → Option β) ⦃l₁ l₂ : List α⦄ (h : l₁ <:+: l₂) :
    filterMap f l₁ <:+: filterMap f l₂ := by
  obtain ⟨xs, ys, rfl⟩ := h
  rw [filterMap_append, filterMap_append]; apply infix_append

grind_pattern IsInfix.filterMap => l₁ <:+: l₂, filterMap f l₁
grind_pattern IsInfix.filterMap => l₁ <:+: l₂, filterMap f l₂

@[simp, grind =] theorem isPrefixOf_iff_prefix [BEq α] [LawfulBEq α] {l₁ l₂ : List α} :
    l₁.isPrefixOf l₂ ↔ l₁ <+: l₂ := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons a l₁ ih =>
    cases l₂ with
    | nil => simp
    | cons a' l₂ => simp [isPrefixOf, ih]

instance [DecidableEq α] (l₁ l₂ : List α) : Decidable (l₁ <+: l₂) :=
  decidable_of_iff (l₁.isPrefixOf l₂) isPrefixOf_iff_prefix

@[simp, grind =] theorem isSuffixOf_iff_suffix [BEq α] [LawfulBEq α] {l₁ l₂ : List α} :
    l₁.isSuffixOf l₂ ↔ l₁ <:+ l₂ := by
  simp [isSuffixOf]

instance [DecidableEq α] (l₁ l₂ : List α) : Decidable (l₁ <:+ l₂) :=
  decidable_of_iff (l₁.isSuffixOf l₂) isSuffixOf_iff_suffix

theorem prefix_iff_eq_append : l₁ <+: l₂ ↔ l₁ ++ drop (length l₁) l₂ = l₂ :=
  ⟨by rintro ⟨r, rfl⟩; rw [drop_left], fun e => ⟨_, e⟩⟩

theorem prefix_iff_eq_take : l₁ <+: l₂ ↔ l₁ = take (length l₁) l₂ :=
  ⟨fun h => append_cancel_right <| (prefix_iff_eq_append.1 h).trans (take_append_drop _ _).symm,
    fun e => e.symm ▸ take_prefix _ _⟩

theorem prefix_iff_exists_append_eq {l₁ l₂ : List α} : l₁ <+: l₂ ↔ ∃ l₃, l₁ ++ l₃ = l₂ :=
  Iff.rfl

theorem prefix_iff_exists_eq_append {l₁ l₂ : List α} : l₁ <+: l₂ ↔ ∃ l₃, l₂ = l₁ ++ l₃ := by
  simp [prefix_iff_exists_append_eq, eq_comm]

-- See `Init.Data.List.Nat.Sublist` for `suffix_iff_eq_append`, `prefix_take_iff`, and `suffix_iff_eq_drop`.

theorem suffix_iff_exists_append_eq {l₁ l₂ : List α} : l₁ <:+ l₂ ↔ ∃ l₃, l₃ ++ l₁ = l₂ :=
  Iff.rfl

theorem suffix_iff_exists_eq_append {l₁ l₂ : List α} : l₁ <:+ l₂ ↔ ∃ l₃, l₂ = l₃ ++ l₁ := by
  simp [suffix_iff_exists_append_eq, eq_comm]

theorem suffix_append_self_iff {l₁ l₂ l₃ : List α} : l₁ ++ l₃ <:+ l₂ ++ l₃ ↔ l₁ <:+ l₂ := by
  constructor
  · rintro ⟨t, h⟩
    exact ⟨t, List.append_cancel_right (by rwa [← List.append_assoc] at h)⟩
  · rintro ⟨t, h⟩
    exact ⟨t, by rw [← List.append_assoc, h]⟩

theorem prefix_self_append_iff {l₁ l₂ l₃ : List α} : l₃ ++ l₁ <+: l₃ ++ l₂ ↔ l₁ <+: l₂ := by
  constructor
  · rintro ⟨t, h⟩
    exact ⟨t, List.append_cancel_left (by rwa [List.append_assoc] at h)⟩
  · rintro ⟨t, h⟩
    exact ⟨t, by rw [List.append_assoc, h]⟩

theorem suffix_append_inj_of_length_eq {l₁ l₂ s₁ s₂ : List α} (hs : s₁.length = s₂.length) :
    l₁ ++ s₁ <:+ l₂ ++ s₂ ↔ l₁ <:+ l₂ ∧ s₁ = s₂ := by
  simp only [suffix_iff_exists_eq_append]
  refine ⟨?_, ?_⟩
  · rintro ⟨l₃, h⟩
    rw [← List.append_assoc] at h
    obtain ⟨rfl, rfl⟩ := List.append_inj' h hs.symm
    refine ⟨⟨l₃, by simp⟩, by simp⟩
  · rintro ⟨⟨l₃, rfl⟩, rfl⟩
    refine ⟨l₃, by simp⟩

theorem prefix_append_inj_of_length_eq {l₁ l₂ s₁ s₂ : List α} (hs : s₁.length = s₂.length) :
    s₁ ++ l₁ <+: s₂ ++ l₂ ↔ s₁ = s₂ ∧ l₁ <+: l₂ := by
  constructor
  · rintro ⟨t, h⟩
    rw [List.append_assoc] at h
    obtain ⟨rfl, rfl⟩ := List.append_inj h.symm hs.symm
    exact ⟨rfl, ⟨t, rfl⟩⟩
  · rintro ⟨rfl, t, rfl⟩
    exact ⟨t, by simp⟩

theorem singleton_suffix_iff_getLast?_eq_some {a : α} {l : List α} : [a] <:+ l ↔ l.getLast? = some a := by
  rw [suffix_iff_exists_eq_append, getLast?_eq_some_iff]

theorem singleton_prefix_iff_head?_eq_some {a : α} {l : List α} : [a] <+: l ↔ l.head? = some a := by
  simp [prefix_iff_exists_eq_append, head?_eq_some_iff]

theorem singleton_prefix_cons_iff {a b : α} {l : List α} : [a] <+: b :: l ↔ a = b := by
  simp

@[simp]
theorem singleton_suffix_append_singleton_iff {a b : α} {l : List α} :
    [a] <:+ l ++ [b] ↔ a = b := by
  refine ⟨fun h => Eq.symm ?_, by rintro rfl; simp⟩
  simpa [List.suffix_iff_exists_eq_append] using h

@[simp]
theorem singleton_suffix_cons_append_singleton_iff {a b c : α} {l : List α} :
    [a] <:+ b :: (l ++ [c]) ↔ a = c := by
  rw [← List.cons_append]
  exact singleton_suffix_append_singleton_iff

theorem infix_append_iff {α : Type u} {l xs ys : List α} : l <:+: xs ++ ys ↔
    l <:+: xs ∨ l <:+: ys ∨ (∃ l₁ l₂, l = l₁ ++ l₂ ∧ l₁ <:+ xs ∧ l₂ <+: ys) := by
  constructor
  · rintro ⟨s, t, ht⟩
    rcases List.append_eq_append_iff.mp ht with ⟨as, hxs, _⟩ | ⟨bs, hsl, hys⟩
    · exact Or.inl ⟨s, as, hxs.symm⟩
    · rcases List.append_eq_append_iff.mp hsl with ⟨cs, hxs', hl⟩ | ⟨ds, _, hbs⟩
      · exact Or.inr (Or.inr ⟨cs, bs, hl,
          List.suffix_iff_exists_eq_append.mpr ⟨s, hxs'⟩,
          List.prefix_iff_exists_eq_append.mpr ⟨t, hys⟩⟩)
      · exact Or.inr (Or.inl ⟨ds, t, by rw [hys, ← hbs]⟩)
  · rintro (⟨s, t, ht⟩ | ⟨s, t, ht⟩ | ⟨l₁, l₂, rfl, hl₁, hl₂⟩)
    · exact ⟨s, t ++ ys, by rw [← List.append_assoc, ht]⟩
    · exact ⟨xs ++ s, t, by
        rw [List.append_assoc] at ht
        rw [List.append_assoc (xs ++ s), List.append_assoc xs, ht]⟩
    · rw [List.suffix_iff_exists_eq_append] at hl₁
      rw [List.prefix_iff_exists_eq_append] at hl₂
      obtain ⟨s, hxs⟩ := hl₁
      obtain ⟨t, hys⟩ := hl₂
      exact ⟨s, t, by rw [← List.append_assoc s l₁, List.append_assoc (s ++ l₁), hxs, hys]⟩

theorem infix_append_iff_ne_nil {α : Type u} {l xs ys : List α} : l <:+: xs ++ ys ↔
    l <:+: xs ∨ l <:+: ys ∨ (∃ l₁ l₂, l₁ ≠ [] ∧ l₂ ≠ [] ∧ l = l₁ ++ l₂ ∧ l₁ <:+ xs ∧ l₂ <+: ys) := by
  rw [List.infix_append_iff]
  constructor
  · rintro (h | h | ⟨l₁, l₂, hl, hl₁, hl₂⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · cases l₁ with
      | nil =>
        simp only [List.nil_append] at hl
        subst hl
        exact Or.inr (Or.inl hl₂.isInfix)
      | cons hd tl =>
        cases l₂ with
        | nil =>
          simp only [List.append_nil] at hl
          subst hl
          exact Or.inl hl₁.isInfix
        | cons hd' tl' =>
          exact Or.inr (Or.inr ⟨_, _, List.cons_ne_nil _ _, List.cons_ne_nil _ _, hl, hl₁, hl₂⟩)
  · rintro (h | h | ⟨l₁, l₂, -, -, hl, hl₁, hl₂⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨l₁, l₂, hl, hl₁, hl₂⟩)

end List
