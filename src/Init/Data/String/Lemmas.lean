/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Char.Lemmas

namespace String

protected theorem data_eq_of_eq {a b : String} (h : a = b) : a.data = b.data :=
  h ▸ rfl
protected theorem ne_of_data_ne {a b : String} (h : a.data ≠ b.data) : a ≠ b :=
  fun h' => absurd (String.data_eq_of_eq h') h

@[simp] protected theorem not_le {a b : String} : ¬ a ≤ b ↔ b < a := Decidable.not_not
@[simp] protected theorem not_lt {a b : String} : ¬ a < b ↔ b ≤ a := Iff.rfl
@[simp] protected theorem le_refl (a : String) : a ≤ a := List.le_refl _
@[simp] protected theorem lt_irrefl (a : String) : ¬ a < a := List.lt_irrefl _

attribute [local instance] Char.notLTTrans Char.notLTAntisymm Char.notLTTotal

protected theorem le_trans {a b c : String} : a ≤ b → b ≤ c → a ≤ c := List.le_trans
protected theorem lt_trans {a b c : String} : a < b → b < c → a < c := List.lt_trans
protected theorem le_total (a b : String) : a ≤ b ∨ b ≤ a := List.le_total
protected theorem le_antisymm {a b : String} : a ≤ b → b ≤ a → a = b := fun h₁ h₂ => String.ext (List.le_antisymm (as := a.data) (bs := b.data) h₁ h₂)
protected theorem lt_asymm {a b : String} (h : a < b) : ¬ b < a := List.lt_asymm h
protected theorem ne_of_lt {a b : String} (h : a < b) : a ≠ b := by
  have := String.lt_irrefl a
  intro h; subst h; contradiction

instance ltIrrefl : Std.Irrefl (· < · : Char → Char → Prop) where
  irrefl := Char.lt_irrefl

instance leRefl : Std.Refl (· ≤ · : Char → Char → Prop) where
  refl := Char.le_refl

instance leTrans : Trans (· ≤ · : Char → Char → Prop) (· ≤ ·) (· ≤ ·) where
  trans := Char.le_trans

instance leAntisymm : Std.Antisymm (· ≤ · : Char → Char → Prop) where
  antisymm _ _ := Char.le_antisymm

instance ltAsymm : Std.Asymm (· < · : Char → Char → Prop) where
  asymm _ _ := Char.lt_asymm

instance leTotal : Std.Total (· ≤ · : Char → Char → Prop) where
  total := Char.le_total

end String
