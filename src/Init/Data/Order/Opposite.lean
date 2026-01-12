/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Order.ClassesExtra
public import Init.Data.Order.LemmasExtra

public section

open Std

set_option doc.verso true
set_option linter.missingDocs true
set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

/--
Inverts an {name}`LE` instance.

The result is an {lean}`LE α` instance where {lit}`a ≤ b` holds when {name}`le` would have
{lit}`b ≤ a` hold.
-/
@[expose]
def LE.opposite (le : LE α) : LE α where
  le a b := b ≤ a

/--
Inverts an {name}`LT` instance.

The result is an {lean}`LT α` instance where {lit}`a < b` holds when {name}`lt` would have
{lit}`b < a` hold.
-/
@[expose]
def LT.opposite (lt : LT α) : LT α where
  lt a b := b < a

/--
Creates a {name}`Max` instance from a {name}`Min` instance.

The result is a {lean}`Max α` instance that uses {lean}`min.min` as its {name}`max` operation.
-/
@[expose]
def Min.oppositeMax (min : Min α) : Max α where
  max a b := Min.min a b

/--
Creates a {name}`Min` instance from a {name}`Max` instance.

The result is a {lean}`Min α` instance that uses {lean}`max.max` as its {name}`min` operation.
-/
@[expose]
def Max.oppositeMin (max : Max α) : Min α where
  min a b := Max.max a b

instance DecidableLE.opposite [i : LE α] [id : DecidableLE α] :
    haveI := i.opposite
    DecidableLE α :=
  fun a b => id b a

instance DecidableLT.opposite [i : LT α] [id : DecidableLT α] :
    haveI := i.opposite
    DecidableLT α :=
  fun a b => id b a

instance LE.instReflOpposite [i : LE α] [Refl (α := α) (· ≤ ·)] :
    haveI := i.opposite
    Refl (α := α) (· ≤ ·) :=
  letI := i.opposite
  { refl a := letI := i; le_refl a }

instance LE.instSymmOpposite [i : LE α] [Symm (α := α) (· ≤ ·)] :
    haveI := i.opposite
    Symm (α := α) (· ≤ ·) :=
  letI := i.opposite
  { symm a b hab := by
      simp only [LE.opposite] at *
      letI := i
      exact Symm.symm b a hab }

instance LE.instAntisymmOpposite [i : LE α] [Antisymm (α := α) (· ≤ ·)] :
    haveI := i.opposite
    Antisymm (α := α) (· ≤ ·) :=
  letI := i.opposite
  { antisymm a b hab hba := by
      simp only [LE.opposite] at *
      letI := i
      exact le_antisymm hba hab }

instance LE.instAsymmOpposite [i : LE α] [Asymm (α := α) (· ≤ ·)] :
    haveI := i.opposite
    Asymm (α := α) (· ≤ ·) :=
  letI := i.opposite
  { asymm a b hab := by
      simp only [LE.opposite] at *
      letI := i
      exact Asymm.asymm b a hab }

instance LE.instTransOpposite [i : LE α] [Trans (· ≤ ·) (· ≤ ·) (· ≤ · : α → α → Prop)] :
    haveI := i.opposite
    Trans (· ≤ ·) (· ≤ ·) (· ≤ · : α → α → Prop) :=
  letI := i.opposite
  { trans hab hbc := by
      simp only [LE.opposite] at *
      letI := i
      exact Trans.trans hbc hab }

instance LE.instTotalOpposite [i : LE α] [Total (α := α) (· ≤ ·)] :
    haveI := i.opposite
    Total (α := α) (· ≤ ·) :=
  letI := i.opposite
  { total a b := letI := i; le_total (a := b) (b := a) }

instance LE.instIrreflOpposite [i : LE α] [Irrefl (α := α) (· ≤ ·)] :
    haveI := i.opposite
    Irrefl (α := α) (· ≤ ·) :=
  letI := i.opposite
  { irrefl a := letI := i; Irrefl.irrefl (r := (· ≤ ·)) a }

instance IsPreorder.opposite [i : LE α] [IsPreorder α] :
    haveI := i.opposite
    IsPreorder α :=
  letI := i.opposite
  { le_refl a := le_refl a
    le_trans _ _ _ := le_trans }

instance IsPartialOrder.opposite [i : LE α] [IsPartialOrder α] :
    haveI := i.opposite
    IsPartialOrder α :=
  letI := i.opposite
  { le_antisymm _ _ := le_antisymm }

instance IsLinearPreorder.opposite [i : LE α] [IsLinearPreorder α] :
    haveI := i.opposite
    IsLinearPreorder α :=
  letI := i.opposite
  { le_total _ _ := le_total }

instance IsLinearOrder.opposite [i : LE α] [IsLinearOrder α] :
    haveI := i.opposite
    IsLinearOrder α :=
  letI := i.opposite; {}

instance LawfulOrderOrd.opposite [il : LE α] [io : Ord α] [LawfulOrderOrd α] :
    haveI := il.opposite
    haveI := io.opposite
    LawfulOrderOrd α :=
  letI := il.opposite
  letI := io.opposite
  { isLE_compare a b := by
      simp only [LE.opposite, Ord.opposite]
      letI := il; letI := io
      apply isLE_compare
    isGE_compare a b := by
      simp only [LE.opposite, Ord.opposite]
      letI := il; letI := io
      apply isGE_compare }

instance LawfulOrderLT.opposite [il : LE α] [it : LT α] [LawfulOrderLT α] :
    haveI := il.opposite
    haveI := it.opposite
    LawfulOrderLT α :=
  letI := il.opposite
  letI := it.opposite
  { lt_iff a b := by
      simp only [LE.opposite, LT.opposite]
      letI := il; letI := it
      exact LawfulOrderLT.lt_iff b a }

instance LawfulOrderBEq.opposite [il : LE α] [ib : BEq α] [LawfulOrderBEq α] :
    haveI := il.opposite
    LawfulOrderBEq α :=
  letI := il.opposite
  { beq_iff_le_and_ge a b := by
      simp only [LE.opposite]
      letI := il; letI := ib
      rw [LawfulOrderBEq.beq_iff_le_and_ge]
      exact and_comm }

instance LawfulOrderInf.opposite [il : LE α] [im : Min α] [LawfulOrderInf α] :
    haveI := il.opposite
    haveI := im.oppositeMax
    LawfulOrderSup α :=
  letI := il.opposite
  letI := im.oppositeMax
  { max_le_iff a b c := by
      simp only [LE.opposite, Min.oppositeMax]
      letI := il; letI := im
      exact LawfulOrderInf.le_min_iff c a b }

instance LawfulOrderMin.opposite [il : LE α] [im : Min α] [LawfulOrderMin α] :
    haveI := il.opposite
    haveI := im.oppositeMax
    LawfulOrderMax α :=
  letI := il.opposite
  letI := im.oppositeMax
  { max_eq_or a b := by
      simp only [Min.oppositeMax]
      letI := il; letI := im
      exact MinEqOr.min_eq_or a b
    max_le_iff a b c := by
      simp only [LE.opposite, Min.oppositeMax]
      letI := il; letI := im
      exact LawfulOrderInf.le_min_iff c a b }

instance LawfulOrderSup.opposite [il : LE α] [im : Max α] [LawfulOrderSup α] :
    haveI := il.opposite
    haveI := im.oppositeMin
    LawfulOrderInf α :=
  letI := il.opposite
  letI := im.oppositeMin
  { le_min_iff a b c := by
      simp only [LE.opposite, Max.oppositeMin]
      letI := il; letI := im
      exact LawfulOrderSup.max_le_iff b c a }

instance LawfulOrderMax.opposite [il : LE α] [im : Max α] [LawfulOrderMax α] :
    haveI := il.opposite
    haveI := im.oppositeMin
    LawfulOrderMin α :=
  letI := il.opposite
  letI := im.oppositeMin
  { min_eq_or a b := by
      simp only [Max.oppositeMin]
      letI := il; letI := im
      exact MaxEqOr.max_eq_or a b
    le_min_iff a b c := by
      simp only [LE.opposite, Max.oppositeMin]
      letI := il; letI := im
      exact LawfulOrderSup.max_le_iff b c a }

instance LawfulOrderLeftLeaningMin.opposite [il : LE α] [im : Min α] [LawfulOrderLeftLeaningMin α] :
    haveI := il.opposite
    haveI := im.oppositeMax
    LawfulOrderLeftLeaningMax α :=
  letI := il.opposite
  letI := im.oppositeMax
  { max_eq_left a b hab := by
      simp only [Min.oppositeMax]
      letI := il; letI := im
      exact LawfulOrderLeftLeaningMin.min_eq_left a b hab
    max_eq_right a b hab := by
      simp only [Min.oppositeMax]
      letI := il; letI := im
      exact LawfulOrderLeftLeaningMin.min_eq_right a b hab }

instance LawfulOrderLeftLeaningMax.opposite [il : LE α] [im : Max α] [LawfulOrderLeftLeaningMax α] :
    haveI := il.opposite
    haveI := im.oppositeMin
    LawfulOrderLeftLeaningMin α :=
  letI := il.opposite
  letI := im.oppositeMin
  { min_eq_left a b hab := by
      simp only [Max.oppositeMin]
      letI := il; letI := im
      exact LawfulOrderLeftLeaningMax.max_eq_left a b hab
    min_eq_right a b hab := by
      simp only [Max.oppositeMin]
      letI := il; letI := im
      exact LawfulOrderLeftLeaningMax.max_eq_right a b hab }
