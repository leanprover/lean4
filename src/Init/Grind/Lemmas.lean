/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Core
import Init.SimpLemmas
import Init.Classical
import Init.ByCases
import Init.Grind.Util

namespace Lean.Grind

theorem intro_with_eq (p p' q : Prop) (he : p = p') (h : p' → q) : p → q :=
  fun hp => h (he.mp hp)

/-! And -/

theorem and_eq_of_eq_true_left {a b : Prop} (h : a = True) : (a ∧ b) = b := by simp [h]
theorem and_eq_of_eq_true_right {a b : Prop} (h : b = True) : (a ∧ b) = a := by simp [h]
theorem and_eq_of_eq_false_left {a b : Prop} (h : a = False) : (a ∧ b) = False := by simp [h]
theorem and_eq_of_eq_false_right {a b : Prop} (h : b = False) : (a ∧ b) = False := by simp [h]

theorem eq_true_of_and_eq_true_left {a b : Prop} (h : (a ∧ b) = True) : a = True := by simp_all
theorem eq_true_of_and_eq_true_right {a b : Prop} (h : (a ∧ b) = True) : b = True := by simp_all

/-! Or -/

theorem or_eq_of_eq_true_left {a b : Prop} (h : a = True) : (a ∨ b) = True := by simp [h]
theorem or_eq_of_eq_true_right {a b : Prop} (h : b = True) : (a ∨ b) = True := by simp [h]
theorem or_eq_of_eq_false_left {a b : Prop} (h : a = False) : (a ∨ b) = b := by simp [h]
theorem or_eq_of_eq_false_right {a b : Prop} (h : b = False) : (a ∨ b) = a := by simp [h]

theorem eq_false_of_or_eq_false_left {a b : Prop} (h : (a ∨ b) = False) : a = False := by simp_all
theorem eq_false_of_or_eq_false_right {a b : Prop} (h : (a ∨ b) = False) : b = False := by simp_all

/-! Not -/

theorem not_eq_of_eq_true {a : Prop} (h : a = True) : (Not a) = False := by simp [h]
theorem not_eq_of_eq_false {a : Prop} (h : a = False) : (Not a) = True := by simp [h]

theorem eq_false_of_not_eq_true {a : Prop} (h : (Not a) = True) : a = False := by simp_all
theorem eq_true_of_not_eq_false {a : Prop} (h : (Not a) = False) : a = True := by simp_all

theorem false_of_not_eq_self {a : Prop} (h : (Not a) = a) : False := by
  by_cases a <;> simp_all

/-! Eq -/

theorem eq_eq_of_eq_true_left {a b : Prop} (h : a = True) : (a = b) = b := by simp [h]
theorem eq_eq_of_eq_true_right {a b : Prop} (h : b = True) : (a = b) = a := by simp [h]

theorem eq_congr  {α : Sort u} {a₁ b₁ a₂ b₂ : α} (h₁ : a₁ = a₂) (h₂ : b₁ = b₂) : (a₁ = b₁) = (a₂ = b₂) := by simp [*]
theorem eq_congr' {α : Sort u} {a₁ b₁ a₂ b₂ : α} (h₁ : a₁ = b₂) (h₂ : b₁ = a₂) : (a₁ = b₁) = (a₂ = b₂) := by rw [h₁, h₂, Eq.comm (a := a₂)]

/-! Forall -/

theorem forall_propagator (p : Prop) (q : p → Prop) (q' : Prop) (h₁ : p = True) (h₂ : q (of_eq_true h₁) = q') : (∀ hp : p, q hp) = q' := by
  apply propext; apply Iff.intro
  · intro h'; exact Eq.mp h₂ (h' (of_eq_true h₁))
  · intro h'; intros; exact Eq.mpr h₂ h'

end Lean.Grind
