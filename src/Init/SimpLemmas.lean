/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

notation, basic datatypes and type classes
-/
prelude
import Init.Core

@[simp] theorem eqSelf (a : α) : (a = a) = True :=
  propext <| Iff.intro (fun _ => trivial) (fun _ => rfl)

theorem ofEqTrue (h : p = True) : p :=
  h ▸ trivial

theorem eqTrue (h : p) : p = True :=
  propext <| Iff.intro (fun _ => trivial) (fun _ => h)

theorem eqFalse (h : ¬ p) : p = False :=
  propext <| Iff.intro (fun h' => absurd h' h) (fun h' => False.elim h')

theorem eqFalse' (h : p → False) : p = False :=
  propext <| Iff.intro (fun h' => absurd h' h) (fun h' => False.elim h')

theorem eqTrueOfDecide {p : Prop} {s : Decidable p} (h : decide p = true) : p = True :=
  propext <| Iff.intro (fun h => trivial) (fun _ => ofDecideEqTrue h)

theorem eqFalseOfDecide {p : Prop} {s : Decidable p} (h : decide p = false) : p = False :=
  propext <| Iff.intro (fun h' => absurd h' (ofDecideEqFalse h)) (fun h => False.elim h)

theorem impCongr {p₁ p₂ : Sort u} {q₁ q₂ : Sort v} (h₁ : p₁ = p₂) (h₂ : q₁ = q₂) : (p₁ → q₁) = (p₂ → q₂) :=
  h₁ ▸ h₂ ▸ rfl

theorem impCongrCtx {p₁ p₂ q₁ q₂ : Prop} (h₁ : p₁ = p₂) (h₂ : p₂ → q₁ = q₂) : (p₁ → q₁) = (p₂ → q₂) :=
  propext <| Iff.intro
    (fun h hp₂ =>
      have p₁ from h₁ ▸ hp₂
      have q₁ from h this
      h₂ hp₂ ▸ this)
    (fun h hp₁ =>
      have hp₂ : p₂ from h₁ ▸ hp₁
      have q₂ from h hp₂
      h₂ hp₂ ▸ this)

theorem forallCongr {α : Sort u} {p q : α → Prop} (h : ∀ a, (p a = q a)) : (∀ a, p a) = (∀ a, q a) :=
  have p = q from funext h
  this ▸ rfl

@[congr]
theorem iteCongr {x y u v : α} {s : Decidable b} [Decidable c] (h₁ : b = c) (h₂ : c → x = u) (h₃ : ¬ c → y = v) : ite b x y = ite c u v := by
  cases Decidable.em c with
  | inl h => rw [ifPos h]; subst b; rw[ifPos h]; exact h₂ h
  | inr h => rw [ifNeg h]; subst b; rw[ifNeg h]; exact h₃ h

theorem Eq.mprProp {p q : Prop} (h₁ : p = q) (h₂ : q) : p :=
  h₁ ▸ h₂

theorem Eq.mprNot {p q : Prop} (h₁ : p = q) (h₂ : ¬q) : ¬p :=
  h₁ ▸ h₂

@[congr]
theorem diteCongr {s : Decidable b} [Decidable c]
        {x : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}
        (h₁ : b = c)
        (h₂ : (h : c)  → x (Eq.mprProp h₁ h) = u h)
        (h₃ : (h : ¬c) → y (Eq.mprNot h₁ h)  = v h)
        : dite b x y = dite c u v := by
  cases Decidable.em c with
  | inl h => rw [difPos h]; subst b; rw [difPos h]; exact h₂ h
  | inr h => rw [difNeg h]; subst b; rw [difNeg h]; exact h₃ h

namespace Lean.Simp

@[simp] theorem Ne_Eq (a b : α) : (a ≠ b) = Not (a = b) := rfl
@[simp] theorem ite_True (a b : α) : (if True then a else b) = a := rfl
@[simp] theorem ite_False (a b : α) : (if False then a else b) = b := rfl
@[simp] theorem And_self (p : Prop) : (p ∧ p) = p := propext <| Iff.intro (fun h => h.1) (fun h => ⟨h, h⟩)
@[simp] theorem And_True (p : Prop) : (p ∧ True) = p := propext <| Iff.intro (fun h => h.1) (fun h => ⟨h, trivial⟩)
@[simp] theorem True_And (p : Prop) : (True ∧ p) = p := propext <| Iff.intro (fun h => h.2) (fun h => ⟨trivial, h⟩)
@[simp] theorem And_False (p : Prop) : (p ∧ False) = False := propext <| Iff.intro (fun h => h.2) (fun h => False.elim h)
@[simp] theorem False_And (p : Prop) : (False ∧ p) = False := propext <| Iff.intro (fun h => h.1) (fun h => False.elim h)
@[simp] theorem Or_self (p : Prop) : (p ∨ p) = p := propext <| Iff.intro (fun | Or.inl h => h | Or.inr h => h) (fun h => Or.inl h)
@[simp] theorem Or_True (p : Prop) : (p ∨ True) = True := propext <| Iff.intro (fun h => trivial) (fun h => Or.inr trivial)
@[simp] theorem True_Or (p : Prop) : (True ∨ p) = True := propext <| Iff.intro (fun h => trivial) (fun h => Or.inl trivial)
@[simp] theorem Or_False (p : Prop) : (p ∨ False) = p := propext <| Iff.intro (fun | Or.inl h => h | Or.inr h => False.elim h) (fun h => Or.inl h)
@[simp] theorem False_Or (p : Prop) : (False ∨ p) = p := propext <| Iff.intro (fun | Or.inr h => h | Or.inl h => False.elim h) (fun h => Or.inr h)
@[simp] theorem Iff_self (p : Prop) : (p ↔ p) = True := propext <| Iff.intro (fun h => trivial) (fun _ => Iff.intro id id)
@[simp] theorem False_arrow (p : Prop) : (False → p) = True := propext <| Iff.intro (fun _ => trivial) (by intros; trivial)
@[simp] theorem arrow_True (p : Prop) : (p → True) = True := propext <| Iff.intro (fun _ => trivial) (by intros; trivial)
@[simp] theorem True_arrow (p : Prop) : (True → p) = p := propext <| Iff.intro (fun h => h trivial) (by intros; trivial)

@[simp] theorem or_false (b : Bool) : (b || false) = b  := by cases b <;> rfl
@[simp] theorem or_true (b : Bool) : (b || true) = true := by cases b <;> rfl
@[simp] theorem false_or (b : Bool) : (false || b) = b  := by cases b <;> rfl
@[simp] theorem true_or (b : Bool) : (true || b) = true := by cases b <;> rfl
@[simp] theorem or_self (b : Bool) : (b || b) = b       := by cases b <;> rfl

@[simp] theorem and_false (b : Bool) : (b && false) = false := by cases b <;> rfl
@[simp] theorem and_true (b : Bool) : (b && true) = b       := by cases b <;> rfl
@[simp] theorem false_and (b : Bool) : (false && b) = false := by cases b <;> rfl
@[simp] theorem true_and (b : Bool) : (true && b) = b       := by cases b <;> rfl
@[simp] theorem and_self (b : Bool) : (b && b) = b          := by cases b <;> rfl

end Lean.Simp
