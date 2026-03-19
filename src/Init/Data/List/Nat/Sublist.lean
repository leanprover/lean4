/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Init.Data.Function
public import Init.Ext
public import Init.NotationExtra
import Init.Data.List.Nat.Basic
import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Sublist
import Init.Data.List.TakeDrop
import Init.Data.Nat.Lemmas
import Init.Omega

public section

/-!
# Further lemmas about `List.IsSuffix` / `List.IsPrefix` / `List.IsInfix`.

These are in a separate file from most of the lemmas about `List.IsSuffix`
as they required importing more lemmas about natural numbers, and use `omega`.
-/

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace List

theorem IsSuffix.getElem {xs ys : List α} (h : xs <:+ ys) {i} (hn : i < xs.length) :
    xs[i] = ys[ys.length - xs.length + i]'(by have := h.length_le; omega) := by
  rw [getElem_eq_getElem_reverse, h.reverse.getElem, getElem_reverse]
  congr
  have := h.length_le
  omega

theorem suffix_iff_getElem? {l₁ l₂ : List α} : l₁ <:+ l₂ ↔
    l₁.length ≤ l₂.length ∧ ∀ i (h : i < l₁.length), l₂[i + l₂.length - l₁.length]? = some l₁[i] := by
  suffices l₁.length ≤ l₂.length ∧ l₁ <:+ l₂ ↔
      l₁.length ≤ l₂.length ∧ ∀ i (h : i < l₁.length), l₂[i + l₂.length - l₁.length]? = some l₁[i] by
    constructor
    · intro h
      exact this.mp ⟨h.length_le, h⟩
    · intro h
      exact (this.mpr h).2
  simp only [and_congr_right_iff]
  intro le
  rw [← reverse_prefix, prefix_iff_getElem?]
  simp only [length_reverse]
  constructor
  · intro w i h
    specialize w (l₁.length - 1 - i) (by omega)
    rw [getElem?_reverse (by omega)] at w
    have p : l₂.length - 1 - (l₁.length - 1 - i) = i + l₂.length - l₁.length := by omega
    rw [p] at w
    rw [w, getElem_reverse]
    congr
    omega
  · intro w i h
    rw [getElem?_reverse]
    specialize w (l₁.length - 1 - i) (by omega)
    have p : l₁.length - 1 - i + l₂.length - l₁.length = l₂.length - 1 - i := by omega
    rw [p] at w
    rw [w, getElem_reverse]
    exact Nat.lt_of_lt_of_le h le

theorem suffix_iff_getElem {l₁ l₂ : List α} :
    l₁ <:+ l₂ ↔ ∃ (_ : l₁.length ≤ l₂.length), ∀ i (_ : i < l₁.length), l₂[i + l₂.length - l₁.length] = l₁[i] := by
  rw [suffix_iff_getElem?]
  constructor
  · rintro ⟨h, w⟩
    refine ⟨h, fun i h => ?_⟩
    specialize w i h
    rw [getElem?_eq_getElem] at w
    simpa using w
  · rintro ⟨h, w⟩
    refine ⟨h, fun i h => ?_⟩
    specialize w i h
    rw [getElem?_eq_getElem]
    simpa using w

theorem infix_iff_getElem? {l₁ l₂ : List α} : l₁ <:+: l₂ ↔
    ∃ k, l₁.length + k ≤ l₂.length ∧ ∀ i (h : i < l₁.length), l₂[i + k]? = some l₁[i] := by
  constructor
  · intro h
    obtain ⟨t, p, s⟩ := infix_iff_suffix_prefix.mp h
    refine ⟨t.length - l₁.length, by have := p.length_le; have := s.length_le; omega, ?_⟩
    rw [suffix_iff_getElem?] at p
    obtain ⟨p', p⟩ := p
    rw [prefix_iff_getElem?] at s
    intro i h
    rw [s _ (by omega)]
    specialize p i (by omega)
    rw [Nat.add_sub_assoc (by omega)] at p
    rw [← getElem?_eq_getElem, p]
  · rintro ⟨k, le, w⟩
    refine ⟨l₂.take k, l₂.drop (k + l₁.length), ?_⟩
    ext1 i
    rw [getElem?_append]
    split
    · rw [getElem?_append]
      split
      · rw [getElem?_take]; simp_all; omega
      · simp_all
        have p : i = (i - k) + k := by omega
        rw [p, w _ (by omega), getElem?_eq_getElem]
        · congr 2
          omega
        · omega
    · rw [getElem?_drop]
      congr
      simp_all
      omega

theorem suffix_iff_eq_append : l₁ <:+ l₂ ↔ take (length l₂ - length l₁) l₂ ++ l₁ = l₂ :=
  ⟨by rintro ⟨r, rfl⟩; simp only [length_append, Nat.add_sub_cancel_right, take_left], fun e =>
    ⟨_, e⟩⟩

@[grind =]
theorem prefix_take_iff {xs ys : List α} {i : Nat} : xs <+: ys.take i ↔ xs <+: ys ∧ xs.length ≤ i := by
  constructor
  · intro h
    constructor
    · exact List.IsPrefix.trans h <| List.take_prefix i ys
    · replace h := h.length_le
      rw [length_take, Nat.le_min] at h
      exact h.left
  · intro ⟨hp, hl⟩
    have hl' := hp.length_le
    rw [List.prefix_iff_eq_take] at *
    rw [hp, List.take_take]
    simp [Nat.min_eq_left, hl, hl']

theorem suffix_iff_eq_drop : l₁ <:+ l₂ ↔ l₁ = drop (length l₂ - length l₁) l₂ :=
  ⟨fun h => append_cancel_left <| (suffix_iff_eq_append.1 h).trans (take_append_drop _ _).symm,
    fun e => e.symm ▸ drop_suffix _ _⟩

theorem prefix_map_iff_of_injective {f : α → β} (hf : Function.Injective f) :
    l₁.map f <+: l₂.map f ↔ l₁ <+: l₂ := by
  simp [prefix_iff_eq_take, ← map_take, map_inj_right hf]

theorem suffix_map_iff_of_injective {f : α → β} (hf : Function.Injective f) :
    l₁.map f <:+ l₂.map f ↔ l₁ <:+ l₂ := by
  simp [suffix_iff_eq_drop, ← map_drop, map_inj_right hf]

@[grind =] theorem prefix_take_le_iff {xs : List α} (hm : i < xs.length) :
    xs.take i <+: xs.take j ↔ i ≤ j := by
  simp only [prefix_iff_eq_take, length_take]
  induction i generalizing xs j with
  | zero => simp [Nat.min_eq_left, Nat.zero_le, take]
  | succ i IH =>
    cases xs with
    | nil => simp_all
    | cons x xs =>
      cases j with
      | zero =>
        simp
      | succ j =>
        simp only [length_cons, Nat.add_lt_add_iff_right] at hm
        simp [← @IH j xs hm, Nat.min_eq_left, Nat.le_of_lt hm]

@[simp] theorem append_left_sublist_self {xs : List α} (ys : List α) : xs ++ ys <+ ys ↔ xs = [] := by
  constructor
  · intro h
    replace h := h.length_le
    simp only [length_append] at h
    have : xs.length = 0 := by omega
    simp_all
  · rintro rfl
    simp
@[simp] theorem append_right_sublist_self (xs : List α) {ys : List α} : xs ++ ys <+ xs ↔ ys = [] := by
  constructor
  · intro h
    replace h := h.length_le
    simp only [length_append] at h
    have : ys.length = 0 := by omega
    simp_all
  · rintro rfl
    simp

theorem append_sublist_of_sublist_left {xs ys zs : List α} (h : zs <+ xs) :
    xs ++ ys <+ zs ↔ ys = [] ∧ xs = zs := by
  constructor
  · intro h'
    have hl := h.length_le
    have hl' := h'.length_le
    simp only [length_append] at hl'
    have : ys.length = 0 := by omega
    simp_all only [Nat.add_zero, length_eq_zero_iff, true_and, append_nil]
    exact Sublist.eq_of_length_le h' hl
  · rintro ⟨rfl, rfl⟩
    simp

theorem append_sublist_of_sublist_right {xs ys zs : List α} (h : zs <+ ys) :
    xs ++ ys <+ zs ↔ xs = [] ∧ ys = zs := by
  constructor
  · intro h'
    have hl := h.length_le
    have hl' := h'.length_le
    simp only [length_append] at hl'
    have : xs.length = 0 := by omega
    simp_all only [Nat.zero_add, length_eq_zero_iff, true_and]
    exact Sublist.eq_of_length_le h' hl
  · rintro ⟨rfl, rfl⟩
    simp

theorem suffix_iff_exists_append {l₁ l₂ : List α} : l₁ <:+ l₂ ↔ ∃ l₃, l₂ = l₃ ++ l₁ := by
  refine ⟨?_, ?_⟩
  · rw [suffix_iff_eq_append]
    intro h
    rw [← h]
    simp
  · rintro ⟨l₃, rfl⟩
    exact suffix_append l₃ l₁

theorem suffix_iff_exists_append_eq {l₁ l₂ : List α} : l₁ <:+ l₂ ↔ ∃ l₃, l₃ ++ l₁ = l₂ :=
  Iff.rfl

theorem suffix_append_self_iff {l₁ l₂ l₃ : List α} : l₁ ++ l₃ <:+ l₂ ++ l₃ ↔ l₁ <:+ l₂ := by
  simp only [suffix_iff_exists_append]
  refine ⟨?_, ?_⟩
  · rintro ⟨l₄, h⟩
    refine ⟨l₄, by simpa [← List.append_assoc] using h⟩
  · rintro ⟨l₄, rfl⟩
    refine ⟨l₄, by simp⟩

theorem prefix_self_append_iff {l₁ l₂ l₃ : List α} : l₃ ++ l₁ <+: l₃ ++ l₂ ↔ l₁ <+: l₂ := by
  constructor
  · rintro ⟨t, h⟩
    exact ⟨t, List.append_cancel_left (by rwa [List.append_assoc] at h)⟩
  · rintro ⟨t, h⟩
    exact ⟨t, by rw [List.append_assoc, h]⟩

theorem suffix_append_inj_of_length_eq {l₁ l₂ s₁ s₂ : List α} (hs : s₁.length = s₂.length) :
    l₁ ++ s₁ <:+ l₂ ++ s₂ ↔ l₁ <:+ l₂ ∧ s₁ = s₂ := by
  simp only [suffix_iff_exists_append]
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
  rw [suffix_iff_exists_append, getLast?_eq_some_iff]

theorem singleton_prefix_iff_head?_eq_some {a : α} {l : List α} : [a] <+: l ↔ l.head? = some a := by
  simp [prefix_iff_exists_eq_append, head?_eq_some_iff]

@[simp]
theorem singleton_prefix_cons_iff {a b : α} {l : List α} : [a] <+: b :: l ↔ a = b := by
  simp [cons_prefix_cons]

@[simp]
theorem singleton_suffix_append_singleton_iff {a b : α} {l : List α} :
    [a] <:+ l ++ [b] ↔ a = b := by
  refine ⟨fun h => Eq.symm ?_, by rintro rfl; simp⟩
  simpa [List.suffix_iff_exists_append] using h

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
          List.suffix_iff_exists_append.mpr ⟨s, hxs'⟩,
          List.prefix_iff_exists_eq_append.mpr ⟨t, hys⟩⟩)
      · exact Or.inr (Or.inl ⟨ds, t, by rw [hys, ← hbs]⟩)
  · rintro (⟨s, t, ht⟩ | ⟨s, t, ht⟩ | ⟨l₁, l₂, rfl, hl₁, hl₂⟩)
    · exact ⟨s, t ++ ys, by rw [← List.append_assoc, ht]⟩
    · exact ⟨xs ++ s, t, by
        rw [List.append_assoc] at ht
        rw [List.append_assoc (xs ++ s), List.append_assoc xs, ht]⟩
    · rw [List.suffix_iff_exists_append] at hl₁
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
