/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fady Adal

Tests for BitVec ByteArray conversion operations.
-/

open BitVec

/-! ## Basic conversions (standard widths) -/

-- 16-bit conversions
#guard (0x1234#16).toBytesLE.data = #[0x34, 0x12]
#guard (0x1234#16).toBytesBE.data = #[0x12, 0x34]

-- 8-bit conversions
#guard (0xAB#8).toBytesLE.data = #[0xAB]
#guard (0xAB#8).toBytesBE.data = #[0xAB]

-- 32-bit conversions
#guard (0xDEADBEEF#32).toBytesLE.data = #[0xEF, 0xBE, 0xAD, 0xDE]
#guard (0xDEADBEEF#32).toBytesBE.data = #[0xDE, 0xAD, 0xBE, 0xEF]

-- 64-bit conversions
#guard (0x0123456789ABCDEF#64).toBytesLE.data = #[0xEF, 0xCD, 0xAB, 0x89, 0x67, 0x45, 0x23, 0x01]
#guard (0x0123456789ABCDEF#64).toBytesBE.data = #[0x01, 0x23, 0x45, 0x67, 0x89, 0xAB, 0xCD, 0xEF]

/-! ## Non-multiple-of-8 widths -/

-- 3-bit value (pads to 1 byte)
#guard (0b101#3).toBytesLE.data = #[0b00000101]
#guard (0b101#3).toBytesBE.data = #[0b00000101]
#guard (0b101#3).toBytesLE.size = 1
#guard (0b101#3).toBytesBE.size = 1

-- 12-bit value (pads to 2 bytes)
#guard (0xABC#12).toBytesLE.data = #[0xBC, 0x0A]
#guard (0xABC#12).toBytesBE.data = #[0x0A, 0xBC]
#guard (0xABC#12).toBytesLE.size = 2
#guard (0xABC#12).toBytesBE.size = 2

-- 20-bit value (pads to 3 bytes)
#guard (0x12345#20).toBytesLE.data = #[0x45, 0x23, 0x01]
#guard (0x12345#20).toBytesBE.data = #[0x01, 0x23, 0x45]
#guard (0x12345#20).toBytesLE.size = 3
#guard (0x12345#20).toBytesBE.size = 3

/-! ## Edge cases -/

-- Empty bitvector (width 0)
#guard (0#0).toBytesLE.size = 0
#guard (0#0).toBytesBE.size = 0

-- Single bit
#guard (0b1#1).toBytesLE.data = #[0x01]
#guard (0b0#1).toBytesLE.data = #[0x00]
#guard (0b1#1).toBytesLE.size = 1
#guard (0b0#1).toBytesLE.size = 1

-- All zeros
#guard (0x0000#16).toBytesLE.data = #[0x00, 0x00]
#guard (0x0000#16).toBytesBE.data = #[0x00, 0x00]

-- All ones
#guard (0xFFFF#16).toBytesLE.data = #[0xFF, 0xFF]
#guard (0xFFFF#16).toBytesBE.data = #[0xFF, 0xFF]

/-! ## Size properties -/

#guard (0x12345678#32).toBytesLE.size = 4
#guard (0x12345678#32).toBytesBE.size = 4
#guard (0x123456#24).toBytesLE.size = 3
#guard (0x123456#24).toBytesBE.size = 3
#guard (0x12345#20).toBytesLE.size = 3  -- rounds up from 2.5 bytes

/-! ## Round trips (LE) -/

#guard ofBytesLE (ByteArray.mk #[0x34, 0x12]) = 0x1234#16
#guard ofBytesLE (ByteArray.mk #[0xAB]) = 0xAB#8
#guard ofBytesLE (ByteArray.mk #[0xEF, 0xBE, 0xAD, 0xDE]) = 0xDEADBEEF#32

#guard ofBytesLE (0x1234#16).toBytesLE = 0x1234#16
#guard ofBytesLE (0xDEADBEEF#32).toBytesLE = 0xDEADBEEF#32
#guard ofBytesLE (0xAB#8).toBytesLE = 0xAB#8

-- Non-multiple-of-8 round trips
#guard ofBytesLE (0xABC#12).toBytesLE = 0xABC#16
#guard ofBytesLE (0x12345#20).toBytesLE = 0x12345#24
#guard ofBytesLE (0b101#3).toBytesLE = 0b101#8

/-! ## Round trips (BE) -/

#guard ofBytesBE (ByteArray.mk #[0x12, 0x34]) = 0x1234#16
#guard ofBytesBE (ByteArray.mk #[0xAB]) = 0xAB#8
#guard ofBytesBE (ByteArray.mk #[0xDE, 0xAD, 0xBE, 0xEF]) = 0xDEADBEEF#32

#guard ofBytesBE (0x1234#16).toBytesBE = 0x1234#16
#guard ofBytesBE (0xDEADBEEF#32).toBytesBE = 0xDEADBEEF#32
#guard ofBytesBE (0xAB#8).toBytesBE = 0xAB#8

-- Non-multiple-of-8 round trips
#guard ofBytesBE (0xABC#12).toBytesBE = 0xABC#16
#guard ofBytesBE (0x12345#20).toBytesBE = 0x12345#24
#guard ofBytesBE (0b101#3).toBytesBE = 0b101#8

/-! ## Endianness differences -/

-- Single byte: LE and BE are the same
#guard (0xFF#8).toBytesLE = (0xFF#8).toBytesBE
#guard (0xAB#8).toBytesLE = (0xAB#8).toBytesBE

-- Multi-byte: LE and BE are different (unless palindrome)
#guard (0x00FF#16).toBytesLE.data != (0x00FF#16).toBytesBE.data
#guard (0x1234#16).toBytesLE.data != (0x1234#16).toBytesBE.data


/-! ## Empty ByteArray handling -/

#guard ofBytesLE ByteArray.empty = 0#0

/-! ## Integration with other BitVec operations -/

-- Bitwise operations preserve round-trip
#guard let x := 0b11001100#8
      let y := 0b10101010#8
      ofBytesLE ((x &&& y).toBytesLE) = x &&& y

#guard let x := 0x1234#16
      let y := 0x5678#16
      ofBytesLE ((x ||| y).toBytesLE) = x ||| y

-- Concatenation and ByteArray conversions
#guard let x := 0xAB#8
      let y := 0xCD#8
      (x ++ y).toBytesLE.data = #[0xCD, 0xAB]

#guard let x := 0xAB#8
      let y := 0xCD#8
      (x ++ y).toBytesBE.data = #[0xAB, 0xCD]

/-! ## Large bitvectors -/

-- Size checks for large widths
#guard let x := allOnes 256
      x.toBytesLE.size = 32

#guard let x := allOnes 256
      x.toBytesBE.size = 32
