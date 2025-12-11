/-!
Tests for `String.toNat?` and `String.toInt?` with underscore support.

This ensures that numeric parsing functions accept the same underscore digit separators
that are allowed in Lean numeric literals, for consistency.

See: https://github.com/leanprover/lean4/issues/11538
-/

-- Basic underscore tests for String.Slice.isNat
#guard "1_000".toSlice.isNat = true
#guard "100_000".toSlice.isNat = true
#guard "1_000_000".toSlice.isNat = true
#guard "100_000_000".toSlice.isNat = true

-- Edge cases for isNat
#guard "_123".toSlice.isNat = false  -- Cannot start with underscore
#guard "123_".toSlice.isNat = false  -- Cannot end with underscore
#guard "12__34".toSlice.isNat = false  -- Cannot have consecutive underscores
#guard "1_2_3".toSlice.isNat = true  -- Single underscores are fine

-- toNat? basic tests
#guard "1_000".toSlice.toNat? = some 1000
#guard "100_000".toSlice.toNat? = some 100000
#guard "1_000_000".toSlice.toNat? = some 1000000
#guard "100_000_000".toSlice.toNat? = some 100000000

-- More complex patterns
#guard "1_2_3_4_5".toSlice.toNat? = some 12345
#guard "9_99".toSlice.toNat? = some 999
#guard "5_0_0_0".toSlice.toNat? = some 5000

-- Edge cases that should fail
#guard "_123".toSlice.toNat? = none
#guard "123_".toSlice.toNat? = none
#guard "12__34".toSlice.toNat? = none
#guard "12_3_".toSlice.toNat? = none
#guard "_".toSlice.toNat? = none

-- Verify numeric values are correct
#guard "1_234".toSlice.toNat? = "1234".toSlice.toNat?
#guard "987_654_321".toSlice.toNat? = "987654321".toSlice.toNat?

-- Tests for String.toNat? (not just Slice)
#guard "1_000".toNat? = some 1000
#guard "100_000".toNat? = some 100000
#guard "1_000_000".toNat? = some 1000000
#guard "_123".toNat? = none
#guard "123_".toNat? = none

-- Tests for String.Slice.isInt
#guard "-1_000".toSlice.isInt = true
#guard "-100_000".toSlice.isInt = true
#guard "1_000".toSlice.isInt = true  -- Positive numbers are also ints

-- Edge cases for isInt
#guard "-_123".toSlice.isInt = false  -- Cannot have underscore right after minus
#guard "-123_".toSlice.isInt = false  -- Cannot end with underscore
#guard "-12__34".toSlice.isInt = false  -- Cannot have consecutive underscores

-- toInt? basic tests
#guard "-1_000".toSlice.toInt? = some (-1000)
#guard "-100_000".toSlice.toInt? = some (-100000)
#guard "-1_000_000".toSlice.toInt? = some (-1000000)
#guard "1_000".toSlice.toInt? = some 1000
#guard "100_000".toSlice.toInt? = some 100000

-- Edge cases for toInt?
#guard "-_123".toSlice.toInt? = none
#guard "-123_".toSlice.toInt? = none
#guard "-12__34".toSlice.toInt? = none

-- Verify numeric values are correct
#guard "-1_234".toSlice.toInt? = "-1234".toSlice.toInt?
#guard "987_654_321".toSlice.toInt? = "987654321".toSlice.toInt?

-- Tests for String.toInt? (not just Slice)
#guard "-1_000".toInt? = some (-1000)
#guard "1_000".toInt? = some 1000
#guard "-_123".toInt? = none
#guard "-123_".toInt? = none

-- Compatibility with existing behavior (no underscores)
#guard "0".toNat? = some 0
#guard "123".toNat? = some 123
#guard "".toNat? = none
#guard "-456".toInt? = some (-456)
#guard "789".toInt? = some 789
