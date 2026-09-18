
import Init.Grind
import Init.Data.BitVec
import Init.Data.Fin.Lemmas
import Init.Data.Fin.Bitwise
import Init.Data.UInt
import Init.Data.SInt.Basic

import Init.Grind

-- Shim for prototype names
abbrev BitVec.unsigned {w} (x : BitVec w) : Int := Int.ofNat x.toNat
abbrev BitVec.signed {w} (x : BitVec w) := x.toInt

-- Missing instances in standard Lean
def Fin.lnot {n : Nat} (a : Fin n) : Fin n := ⟨n - 1 - a.val, by have := a.isLt; omega⟩
instance {n : Nat} : Complement (Fin n) where complement := Fin.lnot

@[grind hom] theorem Fin.val_lnot {n : Nat} (a : Fin n) : (~~~a).val = n - 1 - a.val := rfl

-- Compatibility lemmas for ported tests
theorem BitVec.toNat_eq_unsigned {w} (x : BitVec w) : x.toNat = x.unsigned := rfl



example (x0 : UInt8) :
    let x := x0.toUInt16
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    x.toNat = x0.toNat*2^8 :=
    by grind

example (x0 : UInt16) :
    let x := x0.toUInt32
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    x.toNat = x0.toNat*2^8 :=
    by grind

example (x0 : UInt32) :
    let x := x0.toUInt64
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    x.toNat = x0.toNat*2^8 :=
    by grind

/-
example (x0 : UInt16) :
    let x := x0.toUSize
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    let x := x + x
    x.toNat = x0.toNat*2^8 := by
  grind

-- 16 doublings times out
-/
