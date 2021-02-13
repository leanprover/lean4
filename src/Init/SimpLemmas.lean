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

theorem eqTrue (h : p) : p = True :=
  propext <| Iff.intro (fun _ => trivial) (fun _ => h)

theorem eqFalse (h : ¬ p) : p = False :=
  propext <| Iff.intro (fun h' => absurd h' h) (fun h' => False.elim h')

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
theorem iteCongr {x y u v : α} [s : Decidable b] [Decidable c] (h₁ : b = c) (h₂ : c → x = u) (h₃ : ¬ c → y = v) : ite b x y = ite c u v := by
  cases Decidable.em c with
  | inl h => rw [ifPos h]; subst b; rw[ifPos h]; exact h₂ h
  | inr h => rw [ifNeg h]; subst b; rw[ifNeg h]; exact h₃ h

theorem Eq.mprProp {p q : Prop} (h₁ : p = q) (h₂ : q) : p :=
  h₁ ▸ h₂

theorem Eq.mprNot {p q : Prop} (h₁ : p = q) (h₂ : ¬q) : ¬p :=
  h₁ ▸ h₂

@[congr]
theorem diteCongr [s : Decidable b] [Decidable c]
        {x : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}
        (h₁ : b = c)
        (h₂ : (h : c)  → x (Eq.mprProp h₁ h) = u h)
        (h₃ : (h : ¬c) → y (Eq.mprNot h₁ h)  = v h)
        : dite b x y = dite c u v := by
  cases Decidable.em c with
  | inl h => rw [difPos h]; subst b; rw [difPos h]; exact h₂ h
  | inr h => rw [difNeg h]; subst b; rw [difNeg h]; exact h₃ h
