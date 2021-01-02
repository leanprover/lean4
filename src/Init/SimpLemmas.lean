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
