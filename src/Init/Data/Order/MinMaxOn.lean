/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.NotationExtra
public import Init.Data.Order.Lemmas

public def minOn [LE β] [DecidableLE β] (f : α → β) (x y : α) :=
  if f x ≤ f y then x else y

public def maxOn [LE β] [DecidableLE β] (f : α → β) (x y : α) :=
  if f y ≤ f x then x else y

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
