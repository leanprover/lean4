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

@[simp] theorem forIn'_some [Monad m] [LawfulMonad m] (a : α) (b : β) (f : (a' : α) → a' ∈ some a → β → m (ForInStep β)) :
    forIn' (some a) b f = bind (f a rfl b) (fun r => pure (ForInStep.value r)) := by
  simp only [forIn', bind_pure_comp]
  rw [map_eq_pure_bind]
  congr
  funext x
  split <;> rfl

@[simp] theorem forIn_none [Monad m] (b : β) (f : α → β → m (ForInStep β)) :
    forIn none b f = pure b := by
  rfl

@[simp] theorem forIn_some [Monad m] [LawfulMonad m] (a : α) (b : β) (f : α → β → m (ForInStep β)) :
    forIn (some a) b f = bind (f a b) (fun r => pure (ForInStep.value r)) := by
  simp only [forIn, forIn', bind_pure_comp]
  rw [map_eq_pure_bind]
  congr
  funext x
  split <;> rfl

@[simp] theorem forIn'_toList [Monad m] (o : Option α) (b : β) (f : (a : α) → a ∈ o.toList → β → m (ForInStep β)) :
    forIn' o.toList b f = forIn' o b fun a m b => f a (by simpa using m) b := by
  cases o <;> rfl

@[simp] theorem forIn_toList [Monad m] (o : Option α) (b : β) (f : α → β → m (ForInStep β)) :
    forIn o.toList b f = forIn o b f := by
  cases o <;> rfl

@[simp] theorem foldlM_toList [Monad m] [LawfulMonad m] (o : Option β) (a : α) (f : α → β → m α) :
    o.toList.foldlM f a = o.elim (pure a) (fun b => f a b) := by
  cases o <;> simp

@[simp] theorem foldrM_toList [Monad m] [LawfulMonad m] (o : Option β) (a : α) (f : β → α → m α) :
    o.toList.foldrM f a = o.elim (pure a) (fun b => f b a) := by
  cases o <;> simp

@[simp] theorem foldl_toList (o : Option β) (a : α) (f : α → β → α) :
    o.toList.foldl f a = o.elim a (fun b => f a b) := by
  cases o <;> simp

@[simp] theorem foldr_toList (o : Option β) (a : α) (f : β → α → α) :
    o.toList.foldr f a = o.elim a (fun b => f b a) := by
  cases o <;> simp

@[simp]
theorem pairwise_toList {P : α → α → Prop} {o : Option α} : o.toList.Pairwise P := by
  cases o <;> simp

@[simp]
theorem head?_toList {o : Option α} : o.toList.head? = o := by
  cases o <;> simp

end Option
