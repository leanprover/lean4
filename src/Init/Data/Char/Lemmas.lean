/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
import all Init.Data.Char.Basic
public import Init.Data.Char.Basic
public import Init.Ext
import Init.Data.UInt.Lemmas

public section

namespace Char

@[deprecated Char.ext (since := "2025-10-26")]
protected theorem eq_of_val_eq : {a b : Char} → a.val = b.val → a = b
  | ⟨_,_⟩, ⟨_,_⟩, rfl => rfl

theorem le_def {a b : Char} : a ≤ b ↔ a.1 ≤ b.1 := .rfl
theorem lt_def {a b : Char} : a < b ↔ a.1 < b.1 := .rfl

@[deprecated lt_def (since := "2025-10-26")]
theorem lt_iff_val_lt_val {a b : Char} : a < b ↔ a.val < b.val := Iff.rfl

@[simp] protected theorem not_le {a b : Char} : ¬ a ≤ b ↔ b < a := UInt32.not_le
@[simp] protected theorem not_lt {a b : Char} : ¬ a < b ↔ b ≤ a := UInt32.not_lt
@[simp] protected theorem le_refl (a : Char) : a ≤ a := by simp [le_def]
@[simp] protected theorem lt_irrefl (a : Char) : ¬ a < a := by simp
protected theorem le_trans {a b c : Char} : a ≤ b → b ≤ c → a ≤ c := UInt32.le_trans
protected theorem lt_trans {a b c : Char} : a < b → b < c → a < c := UInt32.lt_trans
protected theorem le_total (a b : Char) : a ≤ b ∨ b ≤ a := UInt32.le_total a.1 b.1
protected theorem le_antisymm {a b : Char} : a ≤ b → b ≤ a → a = b :=
  fun h₁ h₂ => Char.ext (UInt32.le_antisymm h₁ h₂)
protected theorem lt_asymm {a b : Char} (h : a < b) : ¬ b < a := UInt32.lt_asymm h
protected theorem ne_of_lt {a b : Char} (h : a < b) : a ≠ b := Char.ne_of_val_ne (UInt32.ne_of_lt h)

instance ltIrrefl : Std.Irrefl (· < · : Char → Char → Prop) where
  irrefl := Char.lt_irrefl

instance leRefl : Std.Refl (· ≤ · : Char → Char → Prop) where
  refl := Char.le_refl

instance leTrans : Trans (· ≤ · : Char → Char → Prop) (· ≤ ·) (· ≤ ·) where
  trans := Char.le_trans

instance ltTrans : Trans (· < · : Char → Char → Prop) (· < ·) (· < ·) where
  trans := Char.lt_trans

-- This instance is useful while setting up instances for `String`.
@[implicit_reducible]
def notLTTrans : Trans (¬ · < · : Char → Char → Prop) (¬ · < ·) (¬ · < ·) where
  trans h₁ h₂ := by simpa using Char.le_trans (by simpa using h₂) (by simpa using h₁)

instance leAntisymm : Std.Antisymm (· ≤ · : Char → Char → Prop) where
  antisymm _ _ := Char.le_antisymm

-- This instance is useful while setting up instances for `String`.
instance ltTrichotomous : Std.Trichotomous (· < · : Char → Char → Prop) where
  trichotomous _ _ h₁ h₂ := Char.le_antisymm (by simpa using h₂) (by simpa using h₁)

@[deprecated ltTrichotomous (since := "2025-10-27")]
def notLTAntisymm : Std.Antisymm (¬ · < · : Char → Char → Prop) where
  antisymm := Char.ltTrichotomous.trichotomous

instance ltAsymm : Std.Asymm (· < · : Char → Char → Prop) where
  asymm _ _ := Char.lt_asymm

instance leTotal : Std.Total (· ≤ · : Char → Char → Prop) where
  total := Char.le_total

-- This instance is useful while setting up instances for `String`.
@[deprecated ltAsymm (since := "2025-08-01")]
def notLTTotal : Std.Total (¬ · < · : Char → Char → Prop) where
  total := fun x y => by simpa using Char.le_total y x

@[simp] theorem ofNat_toNat (c : Char) : Char.ofNat c.toNat = c := by
  rw [Char.ofNat, dif_pos]
  rfl

@[simp]
theorem toUInt8_val {c : Char} : c.val.toUInt8 = c.toUInt8 := rfl

@[simp]
theorem toString_eq_singleton {c : Char} : c.toString = String.singleton c := rfl

end Char
