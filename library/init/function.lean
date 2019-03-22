/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Jeremy Avigad, Haitao Zhang

General operations on functions.
-/
prelude
import init.core
universes u₁ u₂ u₃ u₄

namespace Function
variables {α : Sort u₁} {β : Sort u₂} {φ : Sort u₃} {δ : Sort u₄} {ζ : Sort u₁}

@[inline, reducible] def comp (f : β → φ) (g : α → β) : α → φ :=
λ x, f (g x)

infixr  ` ∘ `      := Function.comp

@[inline, reducible] def onFun (f : β → β → φ) (g : α → β) : α → α → φ :=
λ x y, f (g x) (g y)

@[inline, reducible] def combine (f : α → β → φ) (op : φ → δ → ζ) (g : α → β → δ)
  : α → β → ζ :=
λ x y, op (f x y) (g x y)

@[inline, reducible] def const (β : Sort u₂) (a : α) : β → α :=
λ x, a

@[inline, reducible] def swap {φ : α → β → Sort u₃} (f : Π x y, φ x y) : Π y x, φ x y :=
λ y x, f x y

infixl  ` on `:2         := onFun
notation f ` -[` op `]- ` g  := combine f op g

end Function
