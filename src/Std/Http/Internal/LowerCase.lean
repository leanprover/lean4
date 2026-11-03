/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
import Init.Grind
import Init.Data.Int.OfNat
import Init.Data.UInt.Lemmas
public import Init.Data.String.Modify
import Init.Data.String.Lemmas.Modify
public import Init.Data.String.Csimp

@[expose]
public section

/-!
# LowerCase

This module provides predicates and normalization functions for handling ASCII case-insensitivity.
It includes proofs of idempotency for lowercase transformations, as well as utilities for validating
the lowercase state of a String.
-/

namespace Std.Http.Internal

set_option linter.all true

/--
Predicate asserting that a string is in lowercase form.
-/
def IsLowerCase (s : String) : Prop :=
  s.toLower = s

private theorem Char.toLower_eq_self_iff {c : Char} : c.toLower = c ↔ c.isUpper = false := by
  simp only [Char.toLower, Char.isUpper]
  split <;> rename_i h <;> simpa [UInt32.le_iff_toNat_le, Char.ext_iff] using h

private theorem String.toLower_eq_self_iff {s : String} : s.toLower = s ↔ s.toList.any Char.isUpper = false := by
  simp only [String.toLower, ← String.toList_inj, String.toList_map]
  rw (occs := [2]) [← List.map_id s.toList]
  rw [List.map_eq_map_iff]
  simp [Char.toLower_eq_self_iff]

/--
Compiled implementation of `hasNoUpper`. Uppercase characters are ASCII, so it suffices to check
that no UTF-8 byte is in `'A'..'Z'`.
-/
def hasNoUpperImpl (s : String) : Bool :=
  go 0
where
  /-- Checks the bytes from index `i` on. -/
  go (i : Nat) : Bool :=
    if h : i < s.utf8ByteSize then
      let b := s.getUTF8Byte ⟨i⟩ h
      !(b ≥ 'A'.toUInt8 && b ≤ 'Z'.toUInt8) && go (i + 1)
    else
      true
  termination_by s.utf8ByteSize - i

/--
Returns `true` if `s` contains no uppercase character.
-/
@[implemented_by hasNoUpperImpl]
def hasNoUpper (s : String) : Bool :=
  !s.toList.any Char.isUpper

instance : Decidable (IsLowerCase s) :=
  decidable_of_iff (hasNoUpper s = true)
    (by simp [hasNoUpper, IsLowerCase, String.toLower_eq_self_iff])

namespace IsLowerCase

private theorem Char.toLower_idempotent (c : Char) : c.toLower.toLower = c.toLower := by
  simp only [Char.toLower]
  split
  · split
    · next h1 h2 =>
      simp only [UInt32.le_iff_toNat_le, UInt32.toNat_add, seval] at h1 h2
      omega
    · simp
  · rfl

/--
Proof that applying `toLower` to any string results in a string that satisfies the `IsLowerCase`
predicate.
-/
theorem isLowerCase_toLower {s : String} : IsLowerCase s.toLower := by
  unfold IsLowerCase String.toLower
  rw [String.map_map, Function.comp_def]
  simp [Char.toLower_idempotent]

theorem isLowerCase_empty : IsLowerCase "" := by
  simp [IsLowerCase, String.toLower]

end IsLowerCase

end Std.Http.Internal
