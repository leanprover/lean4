/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.List.Sublist
import Init.Data.List.Nat.TakeDrop
import Init.Data.Nat.Lemmas

/-!
# Further lemmas about `List.IsSuffix` / `List.IsPrefix` / `List.IsInfix`.

These are in a separate file from most of the lemmas about `List.IsSuffix`
as they required importing more lemmas about natural numbers, and use `omega`.
-/

namespace List

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

end List
