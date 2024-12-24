/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Core
import Init.SimpLemmas
import Init.Classical

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

/-! Eq -/

theorem eq_eq_of_eq_true_left {a b : Prop} (h : a = True) : (a = b) = b := by simp [h]
theorem eq_eq_of_eq_true_right {a b : Prop} (h : b = True) : (a = b) = a := by simp [h]

end Lean.Grind
