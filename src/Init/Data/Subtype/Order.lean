/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Order.Classes
import Init.Data.Order.Lemmas
import Init.Ext

namespace Subtype
open Std

public instance instLE {α : Type u} [LE α] {P : α → Prop} : LE (Subtype P) where
  le a b := a.val ≤ b.val

public instance instLT {α : Type u} [LT α] {P : α → Prop} : LT (Subtype P) where
  lt a b := a.val < b.val

public instance instLawfulOrderLT {α : Type u} [LT α] [LE α] [LawfulOrderLT α]
    {P : α → Prop} : LawfulOrderLT (Subtype P) where
  lt_iff a b := by simp [LT.lt, LE.le, LawfulOrderLT.lt_iff]

public instance instMin {α : Type u} [Min α] [MinEqOr α] {P : α → Prop} : Min (Subtype P) where
  min a b := ⟨Min.min a.val b.val, MinEqOr.elim a.property b.property⟩

public instance instMax {α : Type u} [Max α] [MaxEqOr α] {P : α → Prop} : Max (Subtype P) where
  max a b := ⟨max a.val b.val, MaxEqOr.elim a.property b.property⟩

public instance instReflLE {α : Type u} [LE α] [i : Refl (α := α) (· ≤ ·)] {P : α → Prop} :
    Refl (α := Subtype P) (· ≤ ·) where
  refl a := i.refl a.val

public instance instAntisymmLE {α : Type u} [LE α] [i : Antisymm (α := α) (· ≤ ·)] {P : α → Prop} :
    Antisymm (α := Subtype P) (· ≤ ·) where
  antisymm a b hab hba := private Subtype.ext <| i.antisymm a.val b.val hab hba

public instance instTotalLE {α : Type u} [LE α] [i : Total (α := α) (· ≤ ·)] {P : α → Prop} :
    Total (α := Subtype P) (· ≤ ·) where
  total a b := i.total a.val b.val

public instance instTransLE {α : Type u} [LE α] [i : Trans (α := α) (· ≤ ·) (· ≤ ·) (· ≤ ·)]
    {P : α → Prop} :
    Trans (α := Subtype P) (· ≤ ·) (· ≤ ·) (· ≤ ·) where
  trans := i.trans

public instance instMinEqOr {α : Type u} [Min α] [MinEqOr α] {P : α → Prop} :
    MinEqOr (Subtype P) where
  min_eq_or a b := by
    cases min_eq_or (a := a.val) (b := b.val) <;> rename_i h
    · exact Or.inl <| Subtype.ext h
    · exact Or.inr <| Subtype.ext h

public instance instLawfulOrderMin {α : Type u} [LE α] [Min α] [LawfulOrderMin α] {P : α → Prop} :
    LawfulOrderMin (Subtype P) where
  le_min_iff _ _ _ := by
    exact le_min_iff (α := α)

public instance instMaxEqOr {α : Type u} [Max α] [MaxEqOr α] {P : α → Prop} :
    MaxEqOr (Subtype P) where
  max_eq_or a b := by
    cases max_eq_or (a := a.val) (b := b.val) <;> rename_i h
    · exact Or.inl <| Subtype.ext h
    · exact Or.inr <| Subtype.ext h

public instance instLawfulOrderMax {α : Type u} [LE α] [Max α] [LawfulOrderMax α] {P : α → Prop} :
    LawfulOrderMax (Subtype P) where
  max_le_iff _ _ _ := by
    open Classical.Order in
    exact max_le_iff (α := α)

public instance instIsPreorder {α : Type u} [LE α] [IsPreorder α] {P : α → Prop} :
    IsPreorder (Subtype P) :=
  IsPreorder.of_le

public instance instIsLinearPreorder {α : Type u} [LE α] [IsLinearPreorder α] {P : α → Prop} :
    IsLinearPreorder (Subtype P) :=
  IsLinearPreorder.of_le

public instance instIsPartialOrder {α : Type u} [LE α] [IsPartialOrder α] {P : α → Prop} :
    IsPartialOrder (Subtype P) :=
  IsPartialOrder.of_le

public instance instIsLinearOrder {α : Type u} [LE α] [IsLinearOrder α] {P : α → Prop} :
    IsLinearOrder (Subtype P) :=
  IsLinearOrder.of_le

end Subtype
