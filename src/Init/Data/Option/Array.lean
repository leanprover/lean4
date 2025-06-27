/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
import Init.Data.Array.Lemmas
import Init.Data.Option.List
import all Init.Data.Option.Instances

namespace Option

@[simp, grind] theorem mem_toArray {a : α} {o : Option α} : a ∈ o.toArray ↔ o = some a := by
  cases o <;> simp [eq_comm]

@[simp, grind] theorem forIn'_toArray [Monad m] (o : Option α) (b : β) (f : (a : α) → a ∈ o.toArray → β → m (ForInStep β)) :
    forIn' o.toArray b f = forIn' o b fun a m b => f a (by simpa using m) b := by
  cases o <;> simp <;> rfl

@[simp, grind] theorem forIn_toArray [Monad m] (o : Option α) (b : β) (f : α → β → m (ForInStep β)) :
    forIn o.toArray b f = forIn o b f := by
  cases o <;> simp <;> rfl

@[simp, grind] theorem foldlM_toArray [Monad m] [LawfulMonad m] (o : Option β) (a : α) (f : α → β → m α) :
    o.toArray.foldlM f a = o.elim (pure a) (fun b => f a b) := by
  cases o <;> simp

@[simp, grind] theorem foldrM_toArray [Monad m] [LawfulMonad m] (o : Option β) (a : α) (f : β → α → m α) :
    o.toArray.foldrM f a = o.elim (pure a) (fun b => f b a) := by
  cases o <;> simp

@[simp, grind] theorem foldl_toArray (o : Option β) (a : α) (f : α → β → α) :
    o.toArray.foldl f a = o.elim a (fun b => f a b) := by
  cases o <;> simp

@[simp, grind] theorem foldr_toArray (o : Option β) (a : α) (f : β → α → α) :
    o.toArray.foldr f a = o.elim a (fun b => f b a) := by
  cases o <;> simp

@[simp, grind =]
theorem toList_toArray {o : Option α} : o.toArray.toList = o.toList := by
  cases o <;> simp

@[simp, grind =]
theorem toArray_toList {o : Option α} : o.toList.toArray = o.toArray := by
  cases o <;> simp

theorem toArray_filter {o : Option α} {p : α → Bool} :
    (o.filter p).toArray = o.toArray.filter p := by
  rw [← toArray_toList, toList_filter, ← List.filter_toArray, toArray_toList]

theorem toArray_bind {o : Option α} {f : α → Option β} :
    (o.bind f).toArray = o.toArray.flatMap (Option.toArray ∘ f) := by
  cases o <;> simp

theorem toArray_join {o : Option (Option α)} : o.join.toArray = o.toArray.flatMap Option.toArray := by
  simp [toArray_bind, ← bind_id_eq_join]

theorem toArray_map {o : Option α} {f : α → β} : (o.map f).toArray = o.toArray.map f := by
  cases o <;> simp

theorem toArray_min [Min α] {o o' : Option α} :
    (min o o').toArray = o.toArray.zipWith min o'.toArray := by
  cases o <;> cases o' <;> simp

@[simp]
theorem size_toArray_le {o : Option α} : o.toArray.size ≤ 1 := by
  cases o <;> simp

@[grind =]
theorem size_toArray {o : Option α} :
    o.toArray.size = if o.isSome then 1 else 0 := by
  cases o <;> simp

@[simp]
theorem toArray_eq_empty_iff {o : Option α} : o.toArray = #[] ↔ o = none := by
  cases o <;> simp

@[simp]
theorem toArray_eq_singleton_iff {o : Option α} : o.toArray = #[a] ↔ o = some a := by
  cases o <;> simp

theorem size_toArray_eq_zero_iff {o : Option α} :
    o.toArray.size = 0 ↔ o = none := by
  simp

@[simp]
theorem size_toArray_eq_one_iff {o : Option α} :
    o.toArray.size = 1 ↔ o.isSome := by
  cases o <;> simp

theorem size_toArray_choice_eq_one [Nonempty α] : (choice α).toArray.size = 1 := by
  simp

end Option
