/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Char.Basic
import Init.Data.UInt.Lemmas

namespace Char

@[ext] protected theorem ext : {a b : Char} → a.val = b.val → a = b
  | ⟨_,_⟩, ⟨_,_⟩, rfl => rfl

theorem le_def {a b : Char} : a ≤ b ↔ a.1 ≤ b.1 := .rfl
theorem lt_def {a b : Char} : a < b ↔ a.1 < b.1 := .rfl
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
def notLTTrans : Trans (¬ · < · : Char → Char → Prop) (¬ · < ·) (¬ · < ·) where
  trans h₁ h₂ := by simpa using Char.le_trans (by simpa using h₂) (by simpa using h₁)

instance leAntisymm : Std.Antisymm (· ≤ · : Char → Char → Prop) where
  antisymm _ _ := Char.le_antisymm

-- This instance is useful while setting up instances for `String`.
def notLTAntisymm : Std.Antisymm (¬ · < · : Char → Char → Prop) where
  antisymm _ _ h₁ h₂ := Char.le_antisymm (by simpa using h₂) (by simpa using h₁)

instance ltAsymm : Std.Asymm (· < · : Char → Char → Prop) where
  asymm _ _ := Char.lt_asymm

instance leTotal : Std.Total (· ≤ · : Char → Char → Prop) where
  total := Char.le_total

-- This instance is useful while setting up instances for `String`.
def notLTTotal : Std.Total (¬ · < · : Char → Char → Prop) where
  total := fun x y => by simpa using Char.le_total y x

theorem utf8Size_eq (c : Char) : c.utf8Size = 1 ∨ c.utf8Size = 2 ∨ c.utf8Size = 3 ∨ c.utf8Size = 4 := by
  have := c.utf8Size_pos
  have := c.utf8Size_le_four
  omega

@[simp] theorem ofNat_toNat (c : Char) : Char.ofNat c.toNat = c := by
  rw [Char.ofNat, dif_pos]
  rfl

end Char

@[deprecated Char.utf8Size (since := "2024-06-04")] abbrev String.csize := Char.utf8Size
