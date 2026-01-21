/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Markus Himmel
-/
module

prelude
public import Init.Data.Fin.OverflowAware
public import Init.Data.UInt.Basic
import Init.Data.Char.Lemmas
import Init.Data.Char.Order
import Init.Grind
public import Init.Data.Function

set_option doc.verso true

public section

namespace Char

/-- The number of surrogate code points. -/
abbrev numSurrogates : Nat :=
  -- 0xe000 - 0xd800
  2048

/-- The size of the {name}`Char` type. -/
abbrev numCodePoints : Nat :=
  -- 0x110000 - numSurrogates
  1112064

/--
Packs {name}`Char` bijectively into {lean}`Fin Char.numCodePoints` by shifting code points which are
greater than the surrogate code points by the number of surrogate code points.

The inverse of this function is called {name (scope := "Init.Data.Char.Ordinal")}`Char.ofOrdinal`.
-/
def ordinal (c : Char) : Fin Char.numCodePoints :=
  if h : c.val < 0xd800 then
    ⟨c.val.toNat, by grind [UInt32.lt_iff_toNat_lt]⟩
  else
    ⟨c.val.toNat - Char.numSurrogates, have := c.valid; by grind [UInt32.lt_iff_toNat_lt]⟩

/--
Unpacks {lean}`Fin Char.numCodePoints` bijectively to {name}`Char` by shifting code points which are
greater then the surrogate code points by the number of surrogate code points.

The inverse of this function is called {name}`Char.ordinal`.
-/
def ofOrdinal (f : Fin Char.numCodePoints) : Char :=
  if h : (f : Nat) < 0xd800 then
    ⟨UInt32.ofNatLT f (by grind), by grind [UInt32.toNat_ofNatLT]⟩
  else
    ⟨UInt32.ofNatLT (f + Char.numSurrogates) (by grind), by grind [UInt32.toNat_ofNatLT]⟩

/--
Computes the next {name}`Char`, skipping over surrogate code points (which are not valid
{name}`Char`s) as necessary.

This function is specified by its interaction with {name}`Char.ordinal`, see
{name (scope := "Init.Data.Char.Ordinal")}`Char.succ?_eq`.
-/
def succ? (c : Char) : Option Char :=
  if h₀ : c.val < 0xd7ff then
    some ⟨c.val + 1, by grind [UInt32.lt_iff_toNat_lt, UInt32.toNat_add]⟩
  else if h₁ : c.val = 0xd7ff then
    some ⟨0xe000, by decide⟩
  else if h₂ : c.val < 0x10ffff then
    some ⟨c.val + 1, by
      have := c.valid
      simp [← UInt32.toNat_inj, UInt32.lt_iff_toNat_lt, UInt32.toNat_add, UInt32.isValidChar,
        Nat.isValidChar] at *
      omega⟩
  else none

/--
Computes the {name}`m`-th next {name}`Char`, skipping over surrogate code points (which are not
valid {name}`Char`s) as necessary.

This function is specificed by its interaction with {name}`Char.ordinal`, see
{name (scope := "Init.Data.Char.Ordinal")}`Char.succMany?_eq`.
-/
def succMany? (m : Nat) (c : Char) : Option Char :=
  c.ordinal.addNat? m |>.map Char.ofOrdinal

@[simp]
theorem coe_ordinal {c : Char} :
    (c.ordinal : Nat) = if c.val < 0xd800 then c.val.toNat else c.val.toNat - Char.numSurrogates := by
  grind [Char.ordinal]

@[simp]
theorem ordinal_zero : '\x00'.ordinal = 0 := by
  ext
  simp

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
theorem ordinal_comp_ofOrdinal : Char.ordinal ∘ Char.ofOrdinal = id := by
  ext; simp

@[simp]
theorem ofOrdinal_comp_ordinal : Char.ofOrdinal ∘ Char.ordinal = id := by
  ext; simp

@[simp]
theorem ordinal_inj {c d : Char} : c.ordinal = d.ordinal ↔ c = d :=
  ⟨fun h => by simpa using congrArg Char.ofOrdinal h, (· ▸ rfl)⟩

theorem ordinal_injective : Function.Injective Char.ordinal :=
  fun _ _ => ordinal_inj.1

@[simp]
theorem ofOrdinal_inj {f g : Fin Char.numCodePoints} : Char.ofOrdinal f = Char.ofOrdinal g ↔ f = g :=
  ⟨fun h => by simpa using congrArg Char.ordinal h, (· ▸ rfl)⟩

theorem ofOrdinal_injective : Function.Injective Char.ofOrdinal :=
   fun _ _ => ofOrdinal_inj.1

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

theorem succ?_eq {c : Char} : c.succ? = (c.ordinal.addNat? 1).map Char.ofOrdinal := by
  fun_cases Char.succ? with
  | case1 h =>
    rw [Fin.addNat?_eq_some]
    · simp only [coe_ordinal, Option.map_some, Option.some.injEq, Char.ext_iff, val_ofOrdinal,
        UInt32.ofNatLT_add, UInt32.reduceOfNatLT]
      split
      · simp
        grind [UInt32.lt_iff_toNat_lt]
      · grind
    · simp
      grind [UInt32.lt_iff_toNat_lt]
  | case2 =>
    rw [Fin.addNat?_eq_some]
    · simp [*, Char.ext_iff]
      rfl
    · simp [*]
      grind
  | case3 =>
    rw [Fin.addNat?_eq_some]
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
    simp [Fin.addNat?_eq_none_iff]
    have := c.valid
    grind [UInt32.lt_iff_toNat_lt]

theorem map_ordinal_succ? {c : Char} : c.succ?.map ordinal = c.ordinal.addNat? 1 := by
  simp [succ?_eq]

theorem succMany?_eq {m : Nat} {c : Char} :
    c.succMany? m = (c.ordinal.addNat? m).map Char.ofOrdinal := by
  rfl

end Char
