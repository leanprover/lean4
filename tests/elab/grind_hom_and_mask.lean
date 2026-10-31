/-!
Tests for `&&&` with a literal mask in `grind`. The `[grind hom]` rewriter has a builtin
simproc that rewrites `x &&& c` over `Nat`, for a mask `c` of the form `1…10…0`, into
`%`, `/`, and `*` by literals, which `cutsat` supports.
-/

-- All-ones masks: `x &&& (2^n - 1) = x % 2^n`
example (x : Nat) : x &&& 1 = x % 2 := by grind
example (x : Nat) : x &&& 3 = x % 4 := by grind
example (x : Nat) : x &&& 255 = x % 256 := by grind
example (x : Nat) : 255 &&& x = x % 256 := by grind
example (x : Nat) : x &&& 0xffffffffffffffff = x % 2^64 := by grind
example (x : Nat) : x &&& 7 < 8 := by grind
example (x : Nat) (h : x < 32) : x &&& 63 = x := by grind
example (x : Nat) : (x &&& 63) / 8 = x % 64 / 8 := by grind
example (x : Nat) : x &&& 31 = (x &&& 15) + (x &&& 16) := by grind

-- Ones followed by zeros: `x &&& ((2^n - 1) * 2^k) = x / 2^k % 2^n * 2^k`
example (x : Nat) : x &&& 0xe0 = x / 32 % 8 * 32 := by grind
example (x : Nat) : 0xe0 &&& x = x / 32 % 8 * 32 := by grind
example (x : Nat) : x &&& 16 = x / 16 % 2 * 16 := by grind
example (x : Nat) : x &&& 0xe0 ≤ x := by grind
example (x : Nat) : (x &&& 0xe0) % 32 = 0 := by grind
example (x : Nat) : x &&& 0xf0 = (x &&& 0xff) - (x &&& 0xf) := by grind
example (x : Nat) (h : x < 256) : x &&& 0xf0 = x - x % 16 := by grind
example (x : Nat) (h : x < 256) : x &&& 0xfe = 2 * (x / 2) := by grind
example (x : Nat) (h : x < 256) : x &&& 0xff00 = 0 := by grind
example (x : Nat) : x &&& 0xffffffff00000000 = x / 2^32 % 2^32 * 2^32 := by grind

-- Through the `BitVec` and fixed-width integer injections
example (x : BitVec 64) : (x &&& 63#64).toNat = x.toNat % 64 := by grind
example (x : BitVec 64) : (x &&& 63).toNat < 64 := by grind
example (x : BitVec 64) : ((x &&& 31) + (x &&& 31)).toNat < 64 := by grind
example (x : BitVec 8) : (x &&& 0xe0).toNat = x.toNat / 32 % 8 * 32 := by grind
example (x : BitVec 64) : (x &&& ~~~31).toNat = x.toNat / 32 % 576460752303423488 * 32 := by grind
example (x : BitVec 64) : ((x &&& 63#64) >>> 3#64).toNat = (x.toNat % 64) / 8 := by grind
example (x : BitVec 64) : ((x &&& BitVec.ofNat 64 (2^3 - 1)) >>> 3#64).toNat = (x.toNat % 8) / 8 := by grind
example (x : BitVec 8) : x &&& 7 = x % 8 := by grind
example (x : BitVec 8) : x &&& 0xf0 = x - x % 16 := by grind
example (x : UInt64) : x &&& 0xff = x % 256 := by grind
example (x : UInt64) : (x &&& 0xff).toNat < 256 := by grind
example (x : UInt8) : x &&& 0xf0 = x - x % 16 := by grind
example (x : UInt32) : x &&& 0xffff = x % 65536 := by grind
example (x y : UInt64) : (x &&& 0xff) + (y &&& 0xff) < 512 := by grind
example (x : Int8) (h : x &&& 0xC0 = 0) : x &&& 0x40 = 0 := by grind
example (x : Int64) : (x &&& 0xff).toBitVec.toNat < 256 := by grind
