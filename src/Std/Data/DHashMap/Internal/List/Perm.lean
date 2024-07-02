/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Init.Data.List.Lemmas

set_option autoImplicit false

universe u v

variable {α : Type u} {β : Type v}

namespace Std.DHashMap.Internal.List

inductive Perm : List α → List α → Prop where
| refl (l) : Perm l l
| cons {l l'} (a) : Perm l l' → Perm (a::l) (a::l')
| swap {l l'} (a b) : Perm l l' → Perm (a::b::l) (b::a::l)
| trans {l l' l''} : Perm l l' → Perm l' l'' → Perm l l''

theorem Perm.append_right {l₁ l₂ : List α} (l₃ : List α) (h : Perm l₁ l₂) : Perm (l₁ ++ l₃) (l₂ ++ l₃) := by
  induction h
  · exact .refl _
  · next a _ ih => exact .cons a ih
  · next a b _ ih => exact .swap a b ih
  · next ih₁ ih₂ => exact .trans ih₁ ih₂

theorem Perm.symm {l₁ l₂ : List α} (h : Perm l₁ l₂) : Perm l₂ l₁ := by
  induction h
  · exact .refl _
  · exact .cons _ ‹_›
  · exact .swap _ _ ‹_›
  · next ih₁ ih₂ => exact .trans ih₂ ih₁

theorem perm_middle {l₁ l₂ : List α} {a : α} : Perm (l₁ ++ a :: l₂) (a :: (l₁ ++ l₂)) := by
  induction l₁
  · simpa using .refl _
  · next h t ih => exact .trans (.cons _ ih) (.swap _ _ (.refl _))

theorem perm_append_comm {l₁ l₂ : List α} : Perm (l₁ ++ l₂) (l₂ ++ l₁) := by
  induction l₁ generalizing l₂
  · simpa using .refl _
  · next h t ih => exact .trans (.cons _ ih) (Perm.symm perm_middle)

theorem Perm.append_left (l₁ : List α) {l₂ l₃ : List α} (h : Perm l₂ l₃) : Perm (l₁ ++ l₂) (l₁ ++ l₃) :=
  Perm.trans perm_append_comm (Perm.trans (Perm.append_right _ h) perm_append_comm)

theorem Perm.append {l₁ l₂ l₃ l₄ : List α} (h₁ : Perm l₁ l₂) (h₂ : Perm l₃ l₄) : Perm (l₁ ++ l₃) (l₂ ++ l₄) :=
  Perm.trans (Perm.append_right l₃ h₁) (Perm.trans perm_append_comm (Perm.trans (Perm.append_right _ h₂) perm_append_comm))

theorem Perm.length_eq {l l' : List α} (h : Perm l l') : l.length = l'.length := by
  induction h <;> simp_all

@[simp]
theorem not_perm_empty_cons {l : List α} {a : α} : ¬(Perm [] (a::l)) :=
  fun h => by simpa using h.length_eq

@[simp]
theorem not_perm_cons_empty {l : List α} {a : α} : ¬(Perm (a::l) []) :=
  fun h => by simpa using h.length_eq

theorem Perm.isEmpty_eq {l l' : List α} (h : Perm l l') : l.isEmpty = l'.isEmpty := by
  cases l <;> cases l' <;> simp_all

theorem perm_append_comm_assoc (l₁ l₂ l₃ : List α) : Perm (l₁ ++ (l₂ ++ l₃)) (l₂ ++ (l₁ ++ l₃)) := by
  simpa only [List.append_assoc] using perm_append_comm.append_right _

theorem Perm.mem_iff {l₁ l₂ : List α} (h : Perm l₁ l₂) {a : α} : a ∈ l₁ ↔ a ∈ l₂ := by
  induction h <;> simp_all [← or_assoc, Or.comm]

theorem Perm.map (f : α → β) {l₁ l₂ : List α} (h : Perm l₁ l₂) : Perm (l₁.map f) (l₂.map f) := by
  induction h
  · exact .refl _
  · exact .cons _ ‹_›
  . exact .swap _ _ ‹_›
  · exact .trans ‹_› ‹_›

theorem reverse_perm {l : List α} : Perm l.reverse l := by
  induction l
  · simpa using .refl _
  · next h t ih =>
    rw [List.reverse_cons]
    refine Perm.trans perm_append_comm ?_
    simpa only [List.singleton_append] using Perm.cons _ ih

end Std.DHashMap.Internal.List
