/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Markus Himmel
-/
module

prelude
public import Init.Data.Fin.Basic
public import Init.Data.UInt.Basic
import Init.Data.Char.Lemmas
import Init.Data.Char.Order
import Init.Grind

public section

namespace Fin

def succ? (f : Fin n) : Option (Fin n) :=
  if h : f + 1 < n then some ⟨f + 1, h⟩ else none

theorem succ?_eq_some (f : Fin n) (h : f + 1 < n) : f.succ? = some ⟨f + 1, h⟩ := by
  grind [Fin.succ?]

theorem succ?_eq_none (f : Fin n) : f.succ? = none ↔ f = n - 1 := by
  grind [Fin.succ?]

def succMany? (f : Fin n) (m : Nat) : Option (Fin n) :=
  if h : f + m < n then some ⟨f + m, h⟩ else none

end Fin

namespace Char

abbrev numSurrogates : Nat :=
  -- 0xe000 - 0xd800
  2048

abbrev numCodePoints : Nat :=
  -- 0x110000 - numSurrogates
  1112064

def ordinal (c : Char) : Fin Char.numCodePoints :=
  if h : c.val < 0xd800 then
    ⟨c.val.toNat, by grind [UInt32.lt_iff_toNat_lt]⟩
  else
    ⟨c.val.toNat - Char.numSurrogates, have := c.valid; by grind [UInt32.lt_iff_toNat_lt]⟩

@[simp]
theorem coe_ordinal {c : Char} : (c.ordinal : Nat) = if c.val < 0xd800 then c.val.toNat else c.val.toNat - Char.numSurrogates := by
  grind [Char.ordinal]

def ofOrdinal (f : Fin Char.numCodePoints) : Char :=
  if h : (f : Nat) < 0xd800 then
    ⟨UInt32.ofNatLT f (by grind), by grind [UInt32.toNat_ofNatLT]⟩
  else
    ⟨UInt32.ofNatLT (f + Char.numSurrogates) (by grind), by grind [UInt32.toNat_ofNatLT]⟩

@[simp]
theorem val_ofOrdinal {f : Fin Char.numCodePoints} :
    (Char.ofOrdinal f).val = if h : (f : Nat) < 0xd800 then UInt32.ofNatLT f (by grind) else UInt32.ofNatLT (f + Char.numSurrogates) (by grind) := by
  grind [Char.ofOrdinal]

@[simp]
theorem ofOrdinal_ordinal {c : Char} : Char.ofOrdinal c.ordinal = c := by
  ext
  simp
  split
  · grind [UInt32.lt_iff_toNat_lt, UInt32.ofNatLT_toNat]
  · rw [dif_neg]
    · simp [← UInt32.toNat_inj]
      rw [Nat.sub_add_cancel]
      · grind [UInt32.toNat_lt]
      · grind [UInt32.lt_iff_toNat_lt]
    · have := c.valid
      grind [UInt32.lt_iff_toNat_lt]

@[simp]
theorem ordinal_ofOrdinal {f : Fin Char.numCodePoints} : (Char.ofOrdinal f).ordinal = f := by
  ext
  simp
  split
  · rw [if_pos, UInt32.toNat_ofNatLT]
    simpa [UInt32.lt_iff_toNat_lt]
  · rw [if_neg, UInt32.toNat_add, UInt32.toNat_ofNatLT, UInt32.toNat_ofNatLT, Nat.mod_eq_of_lt, Nat.add_sub_cancel]
    · grind
    · simp [UInt32.lt_iff_toNat_lt]
      grind

@[simp]
theorem ordinal_inj {c d : Char} : c.ordinal = d.ordinal ↔ c = d :=
  ⟨fun h => by simpa using congrArg Char.ofOrdinal h, (· ▸ rfl)⟩

@[simp]
theorem ofOrdinal_inj {f g : Fin Char.numCodePoints} : Char.ofOrdinal f = Char.ofOrdinal g ↔ f = g :=
  ⟨fun h => by simpa using congrArg Char.ordinal h, (· ▸ rfl)⟩

theorem ordinal_le_of_le {c d : Char} (h : c ≤ d) : c.ordinal ≤ d.ordinal := by
  have := c.valid
  have := d.valid
  simp [Char.le_def, UInt32.le_iff_toNat_le] at h
  simp [Fin.le_def, UInt32.lt_iff_toNat_lt]
  grind

theorem ofOrdinal_le_of_le {f g : Fin Char.numCodePoints} (h : f ≤ g) : Char.ofOrdinal f ≤ Char.ofOrdinal g := by
  simp [Fin.le_def] at h
  simp [Char.le_def, UInt32.le_iff_toNat_le]
  split
  · simp only [UInt32.toNat_ofNatLT]
    split
    · simpa
    · simp
      grind
  · simp only [UInt32.toNat_add, UInt32.toNat_ofNatLT, Nat.reducePow]
    rw [dif_neg (by grind)]
    simp
    grind

theorem le_iff_ordinal_le {c d : Char} : c ≤ d ↔ c.ordinal ≤ d.ordinal :=
  ⟨ordinal_le_of_le, fun h => by simpa using ofOrdinal_le_of_le h⟩

theorem le_iff_ofOrdinal_le {f g : Fin Char.numCodePoints} : f ≤ g ↔ Char.ofOrdinal f ≤ Char.ofOrdinal g :=
  ⟨ofOrdinal_le_of_le, fun h => by simpa using ordinal_le_of_le h⟩

theorem lt_iff_ordinal_lt {c d : Char} : c < d ↔ c.ordinal < d.ordinal := by
  simp only [Std.lt_iff_le_and_not_ge, le_iff_ordinal_le]

theorem lt_iff_ofOrdinal_lt {f g : Fin Char.numCodePoints} : f < g ↔ Char.ofOrdinal f < Char.ofOrdinal g := by
  simp only [Std.lt_iff_le_and_not_ge, le_iff_ofOrdinal_le]

def succ? (c : Char) : Option Char :=
  if h₀ : c.val < 0xd7ff then
    some ⟨c.val + 1, by grind [UInt32.lt_iff_toNat_lt, UInt32.toNat_add]⟩
  else if h₁ : c.val = 0xd7ff then
    some ⟨0xe000, by decide⟩
  else if h₂ : c.val < 0x10ffff then
    some ⟨c.val + 1, by
      have := c.valid
      simp [← UInt32.toNat_inj, UInt32.lt_iff_toNat_lt, UInt32.toNat_add, UInt32.isValidChar, Nat.isValidChar] at *
      omega⟩
  else none

theorem succ?_eq {c : Char} : c.succ? = c.ordinal.succ?.map Char.ofOrdinal := by
  fun_cases Char.succ? with
  | case1 h =>
    rw [Fin.succ?_eq_some]
    · simp only [coe_ordinal, Option.map_some, Option.some.injEq, Char.ext_iff, val_ofOrdinal,
        UInt32.ofNatLT_add, UInt32.reduceOfNatLT]
      split
      · simp
        grind [UInt32.lt_iff_toNat_lt]
      · grind
    · simp
      grind [UInt32.lt_iff_toNat_lt]
  | case2 =>
    rw [Fin.succ?_eq_some]
    · simp [*, Char.ext_iff]
      rfl
    · simp [*]
      grind
  | case3 =>
    rw [Fin.succ?_eq_some]
    · simp only [coe_ordinal, Option.map_some, Option.some.injEq, Char.ext_iff, val_ofOrdinal,
      UInt32.ofNatLT_add, UInt32.reduceOfNatLT]
      split
      · grind
      · rw [dif_neg]
        · simp [← UInt32.toNat_inj]
          grind [UInt32.lt_iff_toNat_lt, UInt32.toNat_inj]
        · have := c.valid
          grind [UInt32.lt_iff_toNat_lt, UInt32.toNat_inj]
    · simp
      grind [UInt32.lt_iff_toNat_lt]
  | case4 =>
    rw [eq_comm]
    simp [Fin.succ?_eq_none]
    have := c.valid
    grind [UInt32.lt_iff_toNat_lt]

def succMany? (m : Nat) (c : Char) : Option Char :=
  c.ordinal.succMany? m |>.map Char.ofOrdinal

end Char
