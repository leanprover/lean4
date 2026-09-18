
import Init.Grind
import Init.Data.BitVec
import Init.Data.Fin.Lemmas
import Init.Data.Fin.Bitwise
import Init.Data.UInt
import Init.Data.SInt.Basic



-- Shim for prototype names
abbrev BitVec.unsigned {w} (x : BitVec w) : Int := Int.ofNat x.toNat
abbrev BitVec.signed {w} (x : BitVec w) := x.toInt

-- Missing instances in standard Lean
def Fin.lnot {n : Nat} (a : Fin n) : Fin n := ⟨n - 1 - a.val, by have := a.isLt; omega⟩
instance {n : Nat} : Complement (Fin n) where complement := Fin.lnot

@[grind hom] theorem Fin.val_lnot {n : Nat} (a : Fin n) : (~~~a).val = n - 1 - a.val := rfl

-- Compatibility lemmas for ported tests
theorem BitVec.toNat_eq_unsigned {w} (x : BitVec w) : x.toNat = x.unsigned := rfl

example (a : Nat) : (a >>> 3) = a / 8 := by
  grind

example (x : BitVec 64) : (x >>> 3#64).toNat = x.toNat / 8 := by
  grind

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

/-
example (x : BitVec 64) : ((x &&& BitVec.ofNat 64 (2^3 - 1)) >>> 3#64).toNat = (x.toNat % 8) / 8 := by
  grind

-/
example (a : Int) : (a >>> 3) = a / 8 := by
  grind
