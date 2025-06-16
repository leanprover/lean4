/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
import Init.Data.List.Sublist
import Init.Data.List.Nat.Basic
import Init.Data.List.Nat.TakeDrop
import Init.Data.Nat.Lemmas

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

@[deprecated suffix_iff_getElem? (since := "2025-05-27")]
abbrev isSuffix_iff := @suffix_iff_getElem?

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

@[deprecated infix_iff_getElem? (since := "2025-05-27")]
abbrev isInfix_iff := @infix_iff_getElem?

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

@[grind =] theorem prefix_take_le_iff {xs : List α} (hm : i < xs.length) :
    xs.take i <+: xs.take j ↔ i ≤ j := by
  simp only [prefix_iff_eq_take, length_take]
  induction i generalizing xs j with
  | zero => simp [Nat.min_eq_left, eq_self_iff_true, Nat.zero_le, take]
  | succ i IH =>
    cases xs with
    | nil => simp_all
    | cons x xs =>
      cases j with
      | zero =>
        simp
      | succ j =>
        simp only [length_cons, Nat.succ_eq_add_one, Nat.add_lt_add_iff_right] at hm
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
    simp_all only [Nat.zero_add, length_eq_zero_iff, true_and, append_nil]
    exact Sublist.eq_of_length_le h' hl
  · rintro ⟨rfl, rfl⟩
    simp

end List
