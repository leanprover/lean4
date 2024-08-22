/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Char.Basic
import Init.Data.UInt.Lemmas

namespace Char

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
protected theorem lt_asymm {a b : Char} (h : a < b) : ¬ b < a := UInt32.lt_asymm h
protected theorem ne_of_lt {a b : Char} (h : a < b) : a ≠ b := Char.ne_of_val_ne (UInt32.ne_of_lt h)

theorem utf8Size_eq (c : Char) : c.utf8Size = 1 ∨ c.utf8Size = 2 ∨ c.utf8Size = 3 ∨ c.utf8Size = 4 := by
  have := c.utf8Size_pos
  have := c.utf8Size_le_four
  omega

@[simp] theorem ofNat_toNat (c : Char) : Char.ofNat c.toNat = c := by
  rw [Char.ofNat, dif_pos]
  rfl

@[ext] protected theorem ext : {a b : Char} → a.val = b.val → a = b
  | ⟨_,_⟩, ⟨_,_⟩, rfl => rfl

end Char

@[deprecated Char.utf8Size (since := "2024-06-04")] abbrev String.csize := Char.utf8Size
