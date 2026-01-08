/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.NotationExtra
public import Init.Data.Order.Lemmas

/-! ## Definitions -/

/--
Returns either `x` or `y`, the one with the smaller value under `f`.

If `f x ≤ f y`, it returns `x`, and otherwise returns `y`.
-/
public def minOn [LE β] [DecidableLE β] (f : α → β) (x y : α) :=
  if f x ≤ f y then x else y


/--
Returns either `x` or `y`, the one with the greater value under `f`.

If `f x ≤ f y`, it returns `x`, and otherwise returns `y`.
-/
public def maxOn [LE β] [DecidableLE β] (f : α → β) (x y : α) :=
  if f y ≤ f x then x else y

/-! ## `minOn` Lemmas -/

theorem minOn_eq_or [LE β] [DecidableLE β] {f : α → β} {x y : α} :
    minOn f x y = x ∨ minOn f x y = y := by
  rw [minOn]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

@[grind =]
theorem minOn_self [LE β] [DecidableLE β] {f : α → β} {x : α} :
    minOn f x x = x := by
  cases minOn_eq_or (f := f) (x := x) (y := x) <;> assumption

@[grind =]
theorem minOn_eq_left [LE β] [DecidableLE β] {f : α → β} {x y : α} (h : f x ≤ f y) :
    minOn f x y = x := by
  simp [minOn, h]

@[grind =]
theorem minOn_eq_right [LE β] [DecidableLE β] {f : α → β} {x y : α} (h : ¬ f x ≤ f y) :
    minOn f x y = y := by
  simp [minOn, h]

@[grind =>]
theorem apply_minOn_le_left [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {f : α → β}
    {x y : α} : f (minOn f x y) ≤ f x := by
  rw [minOn]
  split
  · apply Std.le_refl
  · exact Std.le_of_not_ge ‹_›

@[grind =>]
theorem apply_minOn_le_right [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {f : α → β}
    {x y : α} : f (minOn f x y) ≤ f y := by
  rw [minOn]
  split
  · assumption
  · apply Std.le_refl

/-! ## `maxOn` Lemmas -/

theorem maxOn_eq_or [LE β] [DecidableLE β] {f : α → β} {x y : α} :
    maxOn f x y = x ∨ maxOn f x y = y := by
  rw [maxOn]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

@[grind =]
theorem maxOn_self [LE β] [DecidableLE β] {f : α → β} {x : α} :
    maxOn f x x = x := by
  cases maxOn_eq_or (f := f) (x := x) (y := x) <;> assumption

@[grind =]
theorem maxOn_eq_left [LE β] [DecidableLE β] {f : α → β} {x y : α} (h : f y ≤ f x) :
    maxOn f x y = x := by
  simp [maxOn, h]

@[grind =]
theorem maxOn_eq_right [LE β] [DecidableLE β] {f : α → β} {x y : α} (h : ¬ f y ≤ f x) :
    maxOn f x y = y := by
  simp [maxOn, h]

@[grind =>]
theorem apply_maxOn_ge_left [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {f : α → β}
    {x y : α} : f x ≤ f (maxOn f x y) := by
  rw [maxOn]
  split
  · apply Std.le_refl
  · exact Std.le_of_not_ge ‹_›

@[grind =>]
theorem apply_maxOn_ge_right [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {f : α → β}
    {x y : α} : f y ≤ f (maxOn f x y) := by
  rw [maxOn]
  split
  · assumption
  · apply Std.le_refl

@[grind =]
public theorem maxOn_assoc [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {f : α → β}
    {x y z : α} : maxOn f (maxOn f x y) z = maxOn f x (maxOn f y z) := by
  open scoped Classical.Order in
  simp only [maxOn]
  split
  · split
    · split
      · rfl
      · rfl
    · split
      · have : ¬ f z ≤ f x := by assumption
        have : f z ≤ f x := Std.le_trans ‹f z ≤ f y› ‹f y ≤ f x›
        contradiction
      · rfl
  · split
    · rfl
    · have : f x < f y := Std.not_le.mp ‹¬ f y ≤ f x›
      have : f y < f z := Std.not_le.mp ‹¬ f z ≤ f y›
      have : f x < f z := Std.lt_trans ‹_› ‹_›
      rw [if_neg]
      exact Std.not_le.mpr ‹_›

@[grind =]
public theorem minOn_assoc [LE β] [DecidableLE β] [Std.IsLinearPreorder β] {f : α → β}
    {x y z : α} : minOn f (minOn f x y) z = minOn f x (minOn f y z) := by
  open scoped Classical.Order in
  simp only [minOn]
  split
  · split
    · split
      · rfl
      · rfl
    · split
      · have : ¬ f x ≤ f z := by assumption
        have : f x ≤ f z := Std.le_trans ‹f x ≤ f y› ‹f y ≤ f z›
        contradiction
      · rfl
  · split
    · rfl
    · have : f z < f y := Std.not_le.mp ‹¬ f y ≤ f z›
      have : f y < f x := Std.not_le.mp ‹¬ f x ≤ f y›
      have : f z < f x := Std.lt_trans ‹_› ‹_›
      rw [if_neg]
      exact Std.not_le.mpr ‹_›
