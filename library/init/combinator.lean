/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
/- Combinator calculus -/
namespace combinator
universe variables u₁ u₂ u₃
def I {α : Type u₁} (a : α) := a
def K {α : Type u₁} {β : Type u₂} (a : α) (b : β) := a
def S {α : Type u₁} {β : Type u₂} {γ : Type u₃} (x : α → β → γ) (y : α → β) (z : α) := x z (y z)
end combinator
