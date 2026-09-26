/-!
Tests for `>>>` by a literal in `grind`, over `Nat`, `Int`, `BitVec`, and `USize`, ported from
the intblasting prototype test suite (#15224). Goals that `grind` cannot prove yet are disabled
and marked with `TODO`.
-/

example (a : Nat) : (a >>> 3) = a / 8 := by
  grind

example (x : BitVec 64) : (x >>> 3#64).toNat = x.toNat / 8 := by
  grind

-- TODO: `grind` fails (`&&&` with a constant mask)
/-
example (x : BitVec 64) : ((x &&& 63#64) >>> 3#64).toNat = (x.toNat % 64) / 8 := by
  grind
-/

example (a : Nat) (h : a < 64) : (a >>> 3) < 8 := by
  grind

example (a : Nat) : (a >>> (1 + 2)) = a / 8 := by
  grind

example (x : BitVec 64) : (x >>> BitVec.ofNat 64 (2 + 1)).toNat = x.toNat / 8 := by
  grind

-- TODO: `grind` fails (`&&&` with a constant mask)
/-
example (x : BitVec 64) : ((x &&& BitVec.ofNat 64 (2^3 - 1)) >>> 3#64).toNat = (x.toNat % 8) / 8 := by
  grind
-/

example (a : Int) : (a >>> 3) = a / 8 := by
  grind

-- TODO: `grind` fails (`USize.toNat` bound)
/-
example (x : USize) : x.toNat >>> 64 = 0 := by
  grind
-/
