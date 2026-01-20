/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module
prelude

public import Init.Data.String

public section

/-!
# Case-Insensitive Utilities

This module provides predicates and normalization functions to handle ASCII case-insensitivity. It
includes proofs of idempotency for lowercase transformations and utilities for validating lowercase
state in both `String` and `ByteArray` types.

These utilities are foundational for protocol elements (like HTTP headers) that require
case-insensitive handling.
-/

namespace Std.Http.Internal

set_option linter.all true

/--
Predicate asserting that a string is already in lowercase normal form.
-/
abbrev String.IsLowerCase (s : String) : Prop :=
  s.toLower = s

namespace String.IsLowerCase

private theorem Char.toLower_toLower (c : Char) : c.toLower.toLower = c.toLower := by
  unfold Char.toLower
  have _hSub : ('a'.val - 'A'.val).toNat = 32 := by native_decide
  have _hZ : 'Z'.val.toNat = 90 := by native_decide
  have _hA : 'A'.val.toNat = 65 := by native_decide
  split <;> rename_i h
  · simp only [UInt32.le_iff_toNat_le] at h
    split <;> rename_i h'
    · simp only [UInt32.le_iff_toNat_le, UInt32.toNat_add] at h'; omega
    · rfl
  · rfl

/--
Proof that applying `toLower` to any string results in a string that
satisfies the `IsLowerCase` predicate.
-/
theorem lower_isLowerCase {s : String} : IsLowerCase s.toLower := by
  unfold IsLowerCase String.toLower
  exact String.map_idempotent Char.toLower_toLower

theorem empty_isLowerCase : IsLowerCase "" := by
  native_decide

instance (x : String) : Decidable (IsLowerCase x) :=
  inferInstanceAs (Decidable (x.toLower = x))

end String.IsLowerCase

/--
Returns the lowercase version of an ASCII byte.
If the byte is not an uppercase ASCII letter (A-Z), it returns the byte unchanged.
-/
@[inline]
def toLower (c : UInt8) : UInt8 :=
  if c ≥ 0x41 ∧ c ≤ 0x5A then c + (0x61 - 0x41) else c

namespace ByteArray

/--
Returns `true` if the byte is not an uppercase ASCII letter.
-/
def isLower (c : UInt8) : Bool :=
  ¬(c ≥ 0x41 ∧ c ≤ 0x5A)

/--
Theorem proving that the result of `toLower` always satisfies the `isLower` predicate.
-/
theorem toLower_isLower {x : UInt8} : isLower (toLower x) := by
  unfold isLower toLower
  split <;> rename_i h
  · have h₀ : 65 ≤ x.toNat := UInt8.ofNat_le_iff (by decide) |>.mp h.left
    have h₁ : x.toNat ≤ 90 := UInt8.le_ofNat_iff (by decide) |>.mp h.right
    have h₄ : 90 < x.toNat + 32 := by omega
    have h₅ : x.toNat + 32 < 256 := by omega
    simp
    exact Or.inr (UInt8.lt_ofNat_iff h₅ |>.mpr h₄)
  · simp [h]

/--
Predicate asserting that all bytes in a `ByteArray` satisfy `isLower`.
-/
abbrev IsLowerCase (s : ByteArray) : Prop :=
  s.data.all isLower

theorem IsLowerCase.empty : IsLowerCase .empty := by
  native_decide

theorem IsLowerCase.push {bs : ByteArray} (h : IsLowerCase bs) (h₁ : isLower c) :
    IsLowerCase (bs.push c) := by
  simpa [IsLowerCase, ByteArray.push, Array.all_push, And.intro h h₁]

/--
Transforms a `ByteArray` into a lowercase version, returning a `Subtype`
containing the new array and a proof that it satisfies `IsLowerCase`.
-/
def IsLowerCase.toLowerCase (x : ByteArray) : { s : ByteArray // IsLowerCase s } :=
  x.foldl (fun ⟨b, p⟩ c => ⟨b.push (toLower c), push p (toLower_isLower)⟩) ⟨ByteArray.empty, IsLowerCase.empty⟩

end ByteArray
end Std.Http.Internal
