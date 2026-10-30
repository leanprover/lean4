/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julia M. Himmel
-/
module

prelude
public import Init.Data.ByteArray.Lex
import Init.Data.String.Basic

open Std

namespace String

public instance : LT String :=
  ⟨fun s₁ s₂ => s₁.toByteArray < s₂.toByteArray⟩

@[extern "lean_string_dec_lt"]
public instance decidableLT (s₁ s₂ : @& String) : Decidable (s₁ < s₂) :=
  inferInstanceAs (Decidable (s₁.toByteArray < s₂.toByteArray))

/--
Non-strict inequality on strings, typically used via the `≤` operator.

`a ≤ b` is defined to mean `¬ b < a`.
-/
@[expose, reducible] public protected def le (a b : String) : Prop := ¬ b < a

public instance : LE String :=
  ⟨String.le⟩

public instance decLE (s₁ s₂ : String) : Decidable (s₁ ≤ s₂) :=
  inferInstanceAs (Decidable (Not _))

@[simp]
public theorem toByteArray_lt_toByteArray_iff {s t : String} :
  s.toByteArray < t.toByteArray ↔ s < t := Iff.rfl

theorem not_lt {s t : String} : ¬ s < t ↔ t ≤ s := Iff.rfl

@[simp]
public theorem toByteArray_le_toByteArray_iff {s t : String} :
    s.toByteArray ≤ t.toByteArray ↔ s ≤ t := by
  simp [← not_lt, ← toByteArray_lt_toByteArray_iff, Std.not_lt]

public instance : LawfulOrderLT String where
  lt_iff a b := by simp [← toByteArray_lt_toByteArray_iff, ← toByteArray_le_toByteArray_iff,
    Std.lt_iff_le_and_not_ge]

/--
Lexicographic comparison of strings
-/
@[extern "lean_string_compare", expose]
public protected def compare (s₁ s₂ : @& String) : Ordering :=
  Ord.compare s₁.toByteArray s₂.toByteArray

public instance : Ord String where
  compare := String.compare

@[simp]
public theorem compare_toByteArray_toByteArray {s t : String} :
    Ord.compare s.toByteArray t.toByteArray = Ord.compare s t := rfl

public instance : LawfulOrderOrd String where
  isLE_compare a b := by simp [← toByteArray_le_toByteArray_iff,
    ← compare_toByteArray_toByteArray, Std.isLE_compare]
  isGE_compare := by simp [← toByteArray_le_toByteArray_iff, ← compare_toByteArray_toByteArray,
    Std.isGE_compare]

public instance : TransOrd String where
  isLE_trans {a b c} := by simpa [← compare_toByteArray_toByteArray] using TransOrd.isLE_trans

public instance : LawfulEqOrd String where
  eq_of_compare {a b} := by simp [← compare_toByteArray_toByteArray, String.toByteArray_inj]

public instance : IsLinearOrder String := .of_ord

public instance : Std.LinearOrderPackage String := .ofLE _ { }

end String
