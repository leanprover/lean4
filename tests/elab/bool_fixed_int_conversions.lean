module

import Init.Data.SInt.Lemmas

/-!
Tests the conversion lemmas from `Bool` to fixed-width integers.
-/

example (b : Bool) : b.toUInt8.toNat = b.toNat := by simp
example (b : Bool) : b.toUInt16.toNat = b.toNat := by simp
example (b : Bool) : b.toUInt32.toNat = b.toNat := by simp
example (b : Bool) : b.toUInt64.toNat = b.toNat := by simp
example (b : Bool) : b.toUSize.toNat = b.toNat := by simp

example (b : Bool) : b.toInt8.toInt = b.toNat := by simp
example (b : Bool) : b.toInt16.toInt = b.toNat := by simp
example (b : Bool) : b.toInt32.toInt = b.toNat := by simp
example (b : Bool) : b.toInt64.toInt = b.toNat := by simp
example (b : Bool) : b.toISize.toInt = b.toNat := by simp
