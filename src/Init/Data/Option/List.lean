/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
import Init.Data.List.Lemmas

namespace Option

@[simp, grind] theorem mem_toList {a : α} {o : Option α} : a ∈ o.toList ↔ o = some a := by
  cases o <;> simp [eq_comm]

@[simp, grind] theorem forIn'_toList [Monad m] (o : Option α) (b : β) (f : (a : α) → a ∈ o.toList → β → m (ForInStep β)) :
    forIn' o.toList b f = forIn' o b fun a m b => f a (by simpa using m) b := by
  cases o <;> rfl

@[simp, grind] theorem forIn_toList [Monad m] (o : Option α) (b : β) (f : α → β → m (ForInStep β)) :
    forIn o.toList b f = forIn o b f := by
  cases o <;> rfl

@[simp, grind] theorem foldlM_toList [Monad m] [LawfulMonad m] (o : Option β) (a : α) (f : α → β → m α) :
    o.toList.foldlM f a = o.elim (pure a) (fun b => f a b) := by
  cases o <;> simp

@[simp, grind] theorem foldrM_toList [Monad m] [LawfulMonad m] (o : Option β) (a : α) (f : β → α → m α) :
    o.toList.foldrM f a = o.elim (pure a) (fun b => f b a) := by
  cases o <;> simp

@[simp, grind] theorem foldl_toList (o : Option β) (a : α) (f : α → β → α) :
    o.toList.foldl f a = o.elim a (fun b => f a b) := by
  cases o <;> simp

@[simp, grind] theorem foldr_toList (o : Option β) (a : α) (f : β → α → α) :
    o.toList.foldr f a = o.elim a (fun b => f b a) := by
  cases o <;> simp

@[simp, grind]
theorem pairwise_toList {P : α → α → Prop} {o : Option α} : o.toList.Pairwise P := by
  cases o <;> simp

@[simp, grind]
theorem head?_toList {o : Option α} : o.toList.head? = o := by
  cases o <;> simp

end Option
