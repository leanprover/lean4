/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
import Init.SimpLemmas
public import Init.Data.Order.Classes
public import Init.Data.Order.Lemmas
import Init.Data.Order.Factories
import Init.Data.Subtype

namespace Std

public instance {α : Type u} [LE α] {P : α → Prop} : LE (Subtype P) where
  le a b := a.val ≤ b.val

public instance {α : Type u} [OrderData α] {P : α → Prop} : OrderData (Subtype P) where
  IsLE a b := OrderData.IsLE a.val b.val

public instance {α : Type u} [Min α] [MinEqOr α] {P : α → Prop} : Min (Subtype P) where
  min a b := ⟨Min.min a.val b.val, MinEqOr.elim a.property b.property⟩

public instance {α : Type u} [LE α] {P : α → Prop} : LE (Subtype P) where
  le a b := a.val ≤ b.val

public instance {α : Type u} [LE α] [OrderData α] [LawfulOrderLE α]
    {P : α → Prop} : LawfulOrderLE (Subtype P) where
  le_iff a b := by simp only [LE.le, OrderData.IsLE, LawfulOrderLE.le_iff]

@[no_expose]
public instance {α : Type u} [LE α] [i : Refl (α := α) (· ≤ ·)] {P : α → Prop} :
    Refl (α := Subtype P) (· ≤ ·) where
  refl a := i.refl a.val

@[no_expose]
public instance {α : Type u} [LE α] [i : Antisymm (α := α) (· ≤ ·)] {P : α → Prop} :
    Antisymm (α := Subtype P) (· ≤ ·) where
  antisymm a b hab hba := Subtype.ext <| i.antisymm a.val b.val hab hba

@[no_expose]
public instance {α : Type u} [LE α] [i : Total (α := α) (· ≤ ·)] {P : α → Prop} :
    Total (α := Subtype P) (· ≤ ·) where
  total a b := i.total a.val b.val

@[no_expose]
public instance {α : Type u} [LE α] [i : Trans (α := α) (· ≤ ·) (· ≤ ·) (· ≤ ·)]
    {P : α → Prop} :
    Trans (α := Subtype P) (· ≤ ·) (· ≤ ·) (· ≤ ·) where
  trans := i.trans

@[no_expose]
public instance {α : Type u} [Min α] [MinEqOr α] {P : α → Prop} :
    MinEqOr (Subtype P) where
  min_eq_or a b := by
    cases min_eq_or (a := a.val) (b := b.val) <;> rename_i h
    · exact Or.inl <| Subtype.ext h
    · exact Or.inr <| Subtype.ext h

@[no_expose]
public instance {α : Type u} [OrderData α] [Min α] [LawfulOrderMin α] {P : α → Prop} :
    LawfulOrderMin (Subtype P) where
  le_min_iff _ _ _ := by
    open Classical.Order in
    simpa [LawfulOrderLE.le_iff] using le_min_iff (α := α)

@[no_expose]
public instance {α : Type u} [OrderData α] [IsPreorder α] {P : α → Prop} :
    IsPreorder (Subtype P) :=
  open scoped Classical.Order in IsPreorder.of_le

@[no_expose]
public instance {α : Type u} [OrderData α] [IsLinearPreorder α] {P : α → Prop} :
    IsLinearPreorder (Subtype P) :=
  open scoped Classical.Order in IsLinearPreorder.of_le

@[no_expose]
public instance {α : Type u} [OrderData α] [IsPartialOrder α] {P : α → Prop} :
    IsPartialOrder (Subtype P) :=
  open scoped Classical.Order in IsPartialOrder.of_le

@[no_expose]
public instance {α : Type u} [OrderData α] [IsLinearOrder α] {P : α → Prop} :
    IsLinearOrder (Subtype P) :=
  open scoped Classical.Order in IsLinearOrder.of_le

end Std
