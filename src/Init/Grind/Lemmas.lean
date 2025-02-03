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

theorem rfl_true : true = true :=
  rfl

theorem intro_with_eq (p p' q : Prop) (he : p = p') (h : p' → q) : p → q :=
  fun hp => h (he.mp hp)

/-! And -/

theorem and_eq_of_eq_true_left {a b : Prop} (h : a = True) : (a ∧ b) = b := by simp [h]
theorem and_eq_of_eq_true_right {a b : Prop} (h : b = True) : (a ∧ b) = a := by simp [h]
theorem and_eq_of_eq_false_left {a b : Prop} (h : a = False) : (a ∧ b) = False := by simp [h]
theorem and_eq_of_eq_false_right {a b : Prop} (h : b = False) : (a ∧ b) = False := by simp [h]

theorem eq_true_of_and_eq_true_left {a b : Prop} (h : (a ∧ b) = True) : a = True := by simp_all
theorem eq_true_of_and_eq_true_right {a b : Prop} (h : (a ∧ b) = True) : b = True := by simp_all

theorem or_of_and_eq_false {a b : Prop} (h : (a ∧ b) = False) : (¬a ∨ ¬b) := by
  by_cases a <;> by_cases b <;> simp_all

/-! Or -/

theorem or_eq_of_eq_true_left {a b : Prop} (h : a = True) : (a ∨ b) = True := by simp [h]
theorem or_eq_of_eq_true_right {a b : Prop} (h : b = True) : (a ∨ b) = True := by simp [h]
theorem or_eq_of_eq_false_left {a b : Prop} (h : a = False) : (a ∨ b) = b := by simp [h]
theorem or_eq_of_eq_false_right {a b : Prop} (h : b = False) : (a ∨ b) = a := by simp [h]

theorem eq_false_of_or_eq_false_left {a b : Prop} (h : (a ∨ b) = False) : a = False := by simp_all
theorem eq_false_of_or_eq_false_right {a b : Prop} (h : (a ∨ b) = False) : b = False := by simp_all

/-! Implies -/

theorem imp_eq_of_eq_false_left {a b : Prop} (h : a = False) : (a → b) = True := by simp [h]
theorem imp_eq_of_eq_true_right {a b : Prop} (h : b = True) : (a → b) = True := by simp [h]
theorem imp_eq_of_eq_true_left {a b : Prop} (h : a = True) : (a → b) = b := by simp [h]

theorem eq_true_of_imp_eq_false {a b : Prop} (h : (a → b) = False) : a = True := by simp_all
theorem eq_false_of_imp_eq_false {a b : Prop} (h : (a → b) = False) : b = False := by simp_all

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

/-! Bool.and -/

theorem Bool.and_eq_of_eq_true_left {a b : Bool} (h : a = true) : (a && b) = b := by simp [h]
theorem Bool.and_eq_of_eq_true_right {a b : Bool} (h : b = true) : (a && b) = a := by simp [h]
theorem Bool.and_eq_of_eq_false_left {a b : Bool} (h : a = false) : (a && b) = false := by simp [h]
theorem Bool.and_eq_of_eq_false_right {a b : Bool} (h : b = false) : (a && b) = false := by simp [h]

theorem Bool.eq_true_of_and_eq_true_left {a b : Bool} (h : (a && b) = true) : a = true := by simp_all
theorem Bool.eq_true_of_and_eq_true_right {a b : Bool} (h : (a && b) = true) : b = true := by simp_all

/-! Bool.or -/

theorem Bool.or_eq_of_eq_true_left {a b : Bool} (h : a = true) : (a || b) = true := by simp [h]
theorem Bool.or_eq_of_eq_true_right {a b : Bool} (h : b = true) : (a || b) = true := by simp [h]
theorem Bool.or_eq_of_eq_false_left {a b : Bool} (h : a = false) : (a || b) = b := by simp [h]
theorem Bool.or_eq_of_eq_false_right {a b : Bool} (h : b = false) : (a || b) = a := by simp [h]
theorem Bool.eq_false_of_or_eq_false_left {a b : Bool} (h : (a || b) = false) : a = false := by
  cases a <;> simp_all
theorem Bool.eq_false_of_or_eq_false_right {a b : Bool} (h : (a || b) = false) : b = false := by
  cases a <;> simp_all

/-! Bool.not -/

theorem Bool.not_eq_of_eq_true {a : Bool} (h : a = true) : (!a) = false := by simp [h]
theorem Bool.not_eq_of_eq_false {a : Bool} (h : a = false) : (!a) = true := by simp [h]
theorem Bool.eq_false_of_not_eq_true {a : Bool} (h : (!a) = true) : a = false := by simp_all
theorem Bool.eq_true_of_not_eq_false {a : Bool} (h : (!a) = false) : a = true := by simp_all

theorem Bool.false_of_not_eq_self {a : Bool} (h : (!a) = a) : False := by
  by_cases a <;> simp_all

/- The following two helper theorems are used to case-split `a = b` representing `iff`. -/
theorem of_eq_eq_true {a b : Prop} (h : (a = b) = True) : (¬a ∨ b) ∧ (¬b ∨ a) := by
  by_cases a <;> by_cases b <;> simp_all
theorem of_eq_eq_false {a b : Prop} (h : (a = b) = False) : (¬a ∨ ¬b) ∧ (b ∨ a) := by
  by_cases a <;> by_cases b <;> simp_all

/-! Forall -/

theorem forall_propagator (p : Prop) (q : p → Prop) (q' : Prop) (h₁ : p = True) (h₂ : q (of_eq_true h₁) = q') : (∀ hp : p, q hp) = q' := by
  apply propext; apply Iff.intro
  · intro h'; exact Eq.mp h₂ (h' (of_eq_true h₁))
  · intro h'; intros; exact Eq.mpr h₂ h'

theorem of_forall_eq_false (α : Sort u) (p : α → Prop) (h : (∀ x : α, p x) = False) : ∃ x : α, ¬ p x := by simp_all

/-! dite -/

theorem dite_cond_eq_true' {α : Sort u} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬ c → α} {r : α} (h₁ : c = True) (h₂ : a (of_eq_true h₁) = r) : (dite c a b) = r := by simp [h₁, h₂]
theorem dite_cond_eq_false' {α : Sort u} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬ c → α} {r : α} (h₁ : c = False) (h₂ : b (of_eq_false h₁) = r) : (dite c a b) = r := by simp [h₁, h₂]

/-! Casts -/

theorem eqRec_heq.{u_1, u_2} {α : Sort u_2} {a : α}
        {motive : (x : α) → a = x → Sort u_1} (v : motive a (Eq.refl a)) {b : α} (h : a = b)
        : HEq (@Eq.rec α a motive v b h) v := by
 subst h; rfl

theorem eqRecOn_heq.{u_1, u_2} {α : Sort u_2} {a : α}
        {motive : (x : α) → a = x → Sort u_1} {b : α} (h : a = b) (v : motive a (Eq.refl a))
        : HEq (@Eq.recOn α a motive b h v) v := by
 subst h; rfl

theorem eqNDRec_heq.{u_1, u_2} {α : Sort u_2} {a : α}
        {motive : α → Sort u_1} (v : motive a) {b : α} (h : a = b)
        : HEq (@Eq.ndrec α a motive v b h) v := by
 subst h; rfl

/-! decide -/

theorem of_decide_eq_true {p : Prop} {_ : Decidable p} : decide p = true → p = True := by simp
theorem of_decide_eq_false {p : Prop} {_ : Decidable p} : decide p = false → p = False := by simp
theorem decide_eq_true {p : Prop} {_ : Decidable p} : p = True → decide p = true := by simp
theorem decide_eq_false {p : Prop} {_ : Decidable p} : p = False → decide p = false := by simp

end Lean.Grind
