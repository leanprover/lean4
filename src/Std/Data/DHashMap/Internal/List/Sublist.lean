/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
set_option autoImplicit false

universe u v

variable {α : Type u} {β : Type v}

namespace Std.DHashMap.Internal.List

inductive Sublist : List α → List α → Prop where
| refl {l} : Sublist l l
| cons {a} {l l'} : Sublist l l' → Sublist (a::l) (a::l')
| cons_right {a} {l l'} : Sublist l l' → Sublist l (a::l')

@[simp]
theorem sublist_nil {l : List α} : Sublist [] l := by
  induction l
  · exact .refl
  · exact .cons_right ‹_›

theorem Sublist.length_le {l₁ l₂ : List α} (h : Sublist l₁ l₂) : l₁.length ≤ l₂.length := by
  induction h <;> simp_all <;> omega

theorem Sublist.of_cons_left {l₁ l₂ : List α} {a : α} (h : Sublist (a::l₁) l₂) : Sublist l₁ l₂ := by
  cases h
  · exact .cons_right .refl
  . exact .cons_right ‹_›
  · next h t ih => exact .cons_right (Sublist.of_cons_left ‹_›)

@[simp]
theorem Sublist.cons_iff {a : α} {l₁ l₂ : List α} : Sublist (a::l₁) (a::l₂) ↔ Sublist l₁ l₂ := by
  refine ⟨fun h => ?_, .cons⟩
  cases h
  · exact .refl
  · exact ‹_›
  · next h =>
    cases l₂
    · simpa using h.length_le
    · next b t => exact Sublist.of_cons_left h

theorem Sublist.map (f : α → β) {l₁ l₂ : List α} (h : Sublist l₁ l₂) : Sublist (l₁.map f) (l₂.map f) := by
  induction h
  · exact .refl
  · exact .cons ‹_›
  · exact .cons_right ‹_›

theorem Sublist.mem {l₁ l₂ : List α} (h : Sublist l₁ l₂) {a : α} : a ∈ l₁ → a ∈ l₂ := by
  induction h
  · exact id
  · next ih =>
    simp only [List.mem_cons]
    rintro (ha|ha)
    · exact Or.inl ha
    · exact Or.inr (ih ha)
  · next ih =>
    simp only [List.mem_cons]
    exact fun ha => Or.inr (ih ha)

theorem erase_sublist [BEq α] (l : List α) (a : α) : Sublist (l.erase a) l := by
  induction l
  · simp
  · next h t ih =>
    simp only [List.erase_cons]
    split
    · exact .cons_right .refl
    · exact .cons ih

theorem filter_sublist (l : List α) {f : α → Bool} : Sublist (l.filter f) l := by
  induction l
  · simp
  · next h t ih =>
    simp only [List.filter_cons]
    split
    · exact .cons ih
    · exact .cons_right ih

end Std.DHashMap.Internal.List
