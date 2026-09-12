/-!
Tests for the wide fixed-width integer accessors on `ByteArray`
(`Init.Data.ByteArray.Pack`). These `#guard`s evaluate the accessors on concrete
inputs, checking values, endianness, the all-or-nothing out-of-bounds behaviour,
and round-trip — complementing the spec-level lemmas in
`Init.Data.ByteArray.Lemmas`.
-/

def a : ByteArray := [0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88].toByteArray

-- Values + endianness (defaulting `!` reads).
#guard a.getUInt16LE! 0 == 0x2211
#guard a.getUInt16BE! 0 == 0x1122
#guard a.getUInt32LE! 0 == 0x44332211
#guard a.getUInt32BE! 0 == 0x11223344
#guard a.getUInt32LE! 2 == 0x66554433
#guard a.getUInt64LE! 0 == 0x8877665544332211
#guard a.getUInt64BE! 0 == 0x1122334455667788
#guard a.getUInt16LE! 6 == 0x8877

-- Proof-carrying `uget`/`get` go through different externs; check they agree.
#guard a.ugetUInt32LE 0 (by decide) == 0x44332211
#guard a.ugetUInt32BE 0 (by decide) == 0x11223344
#guard a.getUInt32LE 2 (by decide) == 0x66554433
#guard a.ugetUInt64LE 0 (by decide) == 0x8877665544332211

-- All-or-nothing out-of-bounds: a partial window reads as `0`.
#guard a.getUInt32LE! 5 == 0          -- 5 + 4 > 8
#guard a.getUInt32LE! 8 == 0
#guard a.getUInt16LE! 7 == 0          -- 7 + 2 > 8
#guard a.getUInt32LE! 1000000 == 0    -- huge offset
#guard a.getUInt64LE! 1 == 0          -- 1 + 8 > 8
#guard a.getUInt32LE! (2 ^ 100) == 0  -- non-scalar (bignum) offset

-- Round-trip: read back what was written.
#guard (a.setUInt16LE! 0 0xBEEF).getUInt16LE! 0 == 0xBEEF
#guard (a.setUInt16BE! 0 0xBEEF).getUInt16BE! 0 == 0xBEEF
#guard (a.setUInt32LE! 0 0xDEADBEEF).getUInt32LE! 0 == 0xDEADBEEF
#guard (a.setUInt32BE! 1 0xDEADBEEF).getUInt32BE! 1 == 0xDEADBEEF
#guard (a.setUInt64LE! 0 0x0123456789ABCDEF).getUInt64LE! 0 == 0x0123456789ABCDEF
#guard (a.usetUInt32LE 0 0xCAFEBABE (by decide)).ugetUInt32LE 0 (by decide) == 0xCAFEBABE

-- Byte order on write: little-endian writes the low byte first.
#guard (a.setUInt16LE! 0 0xBEEF).get! 0 == 0xEF
#guard (a.setUInt16LE! 0 0xBEEF).get! 1 == 0xBE
#guard (a.setUInt16BE! 0 0xBEEF).get! 0 == 0xBE

-- All-or-nothing write: an out-of-range write leaves the array unchanged.
#guard (a.setUInt32LE! 5 0xDEADBEEF) == a
#guard (a.setUInt64LE! 1 0) == a
#guard (a.setUInt32LE! 1000000 0xFF) == a
#guard (a.setUInt32LE! (2 ^ 100) 0xFF) == a   -- non-scalar (bignum) offset

-- Size is preserved by writes.
#guard (a.setUInt32LE! 0 0xDEADBEEF).size == a.size

-- Round-trip for big-endian writes too.
#guard (a.setUInt32BE! 0 0xDEADBEEF).getUInt32BE! 0 == 0xDEADBEEF
#guard (a.setUInt64BE! 0 0x0123456789ABCDEF).getUInt64BE! 0 == 0x0123456789ABCDEF
#guard (a.setUInt16BE! 0 0xBEEF).get! 1 == 0xEF

-- Exact upper boundary: a window ending exactly at `size` is in bounds.
#guard a.getUInt32LE! 4 == 0x88776655           -- 4 + 4 = 8 = size
#guard (a.setUInt32LE! 4 0xDEADBEEF).getUInt32LE! 4 == 0xDEADBEEF

-- Disjoint windows do not interfere.
#guard (a.setUInt16LE! 0 0xFFFF).getUInt16LE! 2 == a.getUInt16LE! 2
#guard (a.setUInt32LE! 4 0xFFFFFFFF).getUInt32LE! 0 == a.getUInt32LE! 0
