/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
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

namespace List

theorem IsSuffix.getElem {x y : List α} (h : x <:+ y) {n} (hn : n < x.length) :
    x[n] = y[y.length - x.length + n]'(by have := h.length_le; omega) := by
  rw [getElem_eq_getElem_reverse, h.reverse.getElem, getElem_reverse]
  congr
  have := h.length_le
  omega

theorem isSuffix_iff : l₁ <:+ l₂ ↔
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
  rw [← reverse_prefix, isPrefix_iff]
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

theorem isInfix_iff : l₁ <:+: l₂ ↔
    ∃ k, l₁.length + k ≤ l₂.length ∧ ∀ i (h : i < l₁.length), l₂[i + k]? = some l₁[i] := by
  constructor
  · intro h
    obtain ⟨t, p, s⟩ := infix_iff_suffix_prefix.mp h
    refine ⟨t.length - l₁.length, by have := p.length_le; have := s.length_le; omega, ?_⟩
    rw [isSuffix_iff] at p
    obtain ⟨p', p⟩ := p
    rw [isPrefix_iff] at s
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

theorem prefix_take_iff {x y : List α} {n : Nat} : x <+: y.take n ↔ x <+: y ∧ x.length ≤ n := by
  constructor
  · intro h
    constructor
    · exact List.IsPrefix.trans h <| List.take_prefix n y
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

theorem prefix_take_le_iff {L : List α} (hm : m < L.length) :
    L.take m <+: L.take n ↔ m ≤ n := by
  simp only [prefix_iff_eq_take, length_take]
  induction m generalizing L n with
  | zero => simp [Nat.min_eq_left, eq_self_iff_true, Nat.zero_le, take]
  | succ m IH =>
    cases L with
    | nil => simp_all
    | cons l ls =>
      cases n with
      | zero =>
        simp
      | succ n =>
        simp only [length_cons, Nat.succ_eq_add_one, Nat.add_lt_add_iff_right] at hm
        simp [← @IH n ls hm, Nat.min_eq_left, Nat.le_of_lt hm]

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
    simp_all only [Nat.add_zero, length_eq_zero, true_and, append_nil]
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
    simp_all only [Nat.zero_add, length_eq_zero, true_and, append_nil]
    exact Sublist.eq_of_length_le h' hl
  · rintro ⟨rfl, rfl⟩
    simp

end List
