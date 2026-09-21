import Init.Grind
import Init.Data.BitVec

/-!
Tests for `BitVec.toNat_ofInt` homomorphism rule in `grind`.
-/

example (i : Int) : (BitVec.ofInt 8 i).toNat = (i % 256).toNat := by grind

abbrev BitVec.unsigned {w} (x : BitVec w) : Int := Int.ofNat x.toNat

example (x y : BitVec 64) (c : BitVec 1) :
    let s := x.unsigned + y.unsigned + c.unsigned
    let l := BitVec.ofInt 64 s
    let h := BitVec.ofInt 1 (s >>> 64)
    s = l.unsigned + 2^64 * h.unsigned := by
  grind
