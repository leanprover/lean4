/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.List.Lemmas

namespace Option

@[simp] theorem mem_toList {a : α} {o : Option α} : a ∈ o.toList ↔ a ∈ o := by
  cases o <;> simp [eq_comm]

@[simp] theorem forIn'_none [Monad m] (b : β) (f : (a : α) → a ∈ none → β → m (ForInStep β)) :
    forIn' none b f = pure b := by
  rfl

@[simp] theorem forIn'_some [Monad m] (a : α) (b : β) (f : (a' : α) → a' ∈ some a → β → m (ForInStep β)) :
    forIn' (some a) b f = bind (f a rfl b) (fun | .done r | .yield r => pure r) := by
  rfl

@[simp] theorem forIn_none [Monad m] (b : β) (f : α → β → m (ForInStep β)) :
    forIn none b f = pure b := by
  rfl

@[simp] theorem forIn_some [Monad m] (a : α) (b : β) (f : α → β → m (ForInStep β)) :
    forIn (some a) b f = bind (f a b) (fun | .done r | .yield r => pure r) := by
  rfl

@[simp] theorem forIn'_toList [Monad m] (o : Option α) (b : β) (f : (a : α) → a ∈ o.toList → β → m (ForInStep β)) :
    forIn' o.toList b f = forIn' o b fun a m b => f a (by simpa using m) b := by
  cases o <;> rfl

@[simp] theorem forIn_toList [Monad m] (o : Option α) (b : β) (f : α → β → m (ForInStep β)) :
    forIn o.toList b f = forIn o b f := by
  cases o <;> rfl

end Option
