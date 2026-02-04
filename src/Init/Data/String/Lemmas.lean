/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Init.Data.String.Lemmas.Splits
public import Init.Data.String.Lemmas.Modify
public import Init.Data.String.Lemmas.Search
public import Init.Data.String.Lemmas.FindPos
public import Init.Data.String.Lemmas.Basic
public import Init.Data.String.Lemmas.Order
import Init.Data.Order.Lemmas
public import Init.Data.String.Basic
import Init.Data.Char.Lemmas
import Init.Data.Char.Order
import Init.Data.List.Lex

public section

open Std

namespace String

@[deprecated toList_inj (since := "2025-10-30")]
protected theorem data_eq_of_eq {a b : String} (h : a = b) : a.toList = b.toList :=
  h ▸ rfl
@[deprecated toList_inj (since := "2025-10-30")]
protected theorem ne_of_data_ne {a b : String} (h : a.toList ≠ b.toList) : a ≠ b := by
  simpa [← toList_inj]

@[simp] protected theorem not_le {a b : String} : ¬ a ≤ b ↔ b < a := Decidable.not_not
@[simp] protected theorem not_lt {a b : String} : ¬ a < b ↔ b ≤ a := Iff.rfl
@[simp] protected theorem le_refl (a : String) : a ≤ a := List.le_refl _
@[simp] protected theorem lt_irrefl (a : String) : ¬ a < a := List.lt_irrefl _

attribute [local instance] Char.notLTTrans Char.ltTrichotomous Char.ltAsymm

protected theorem le_trans {a b c : String} : a ≤ b → b ≤ c → a ≤ c := List.le_trans
protected theorem lt_trans {a b c : String} : a < b → b < c → a < c := List.lt_trans
protected theorem le_total (a b : String) : a ≤ b ∨ b ≤ a := List.le_total _ _
protected theorem le_antisymm {a b : String} : a ≤ b → b ≤ a → a = b := fun h₁ h₂ => String.ext (List.le_antisymm (as := a.toList) (bs := b.toList) h₁ h₂)
protected theorem lt_asymm {a b : String} (h : a < b) : ¬ b < a := List.lt_asymm h
protected theorem ne_of_lt {a b : String} (h : a < b) : a ≠ b := by
  have := String.lt_irrefl a
  intro h; subst h; contradiction

instance instIsLinearOrder : IsLinearOrder String := by
  apply IsLinearOrder.of_le
  case le_antisymm => constructor; apply String.le_antisymm
  case le_trans => constructor; apply String.le_trans
  case le_total => constructor; apply String.le_total

instance : LawfulOrderLT String where
  lt_iff a b := by
    simp [← String.not_le, Decidable.imp_iff_not_or, Std.Total.total]

end String
