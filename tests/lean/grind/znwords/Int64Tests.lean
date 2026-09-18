
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

set_option warn.sorry false

set_option autoImplicit true

-- Arithmetic operations
example (x y : Int64) : x + y - y = x := by grind
example (x y : Int64) : (x + y) * 0 = 0 := by grind
example (x : Int64) : x - x = 0 := by grind
example (x : Int64) : x * 1 = x := by grind
example (x : Int64) : -(-x) = x := by grind
example (x y : Int64) : x - y + y = x := by grind
example (x y : Int64) : (x * y) - (y * x) = 0 := by grind

-- Bitwise operations
example (x : Int64) : x &&& 0 = 0 := by grind
example (x : Int64) : x ||| 0 = x := by grind
example (x : Int64) : x ^^^ 0 = x := by grind
example (x : Int64) : x ^^^ x = 0 := by grind
example (x : Int64) : x &&& x = x := by grind
example (x : Int64) : x ||| x = x := by grind
example (x : Int64) : ~~~(~~~x) = x := by grind

-- Shifts
example (x : Int64) : x <<< 1 = x + x := by grind
example (x : Int64) : x <<< 2 = x * 4 := by grind
example (x : Int64) : x <<< 3 = x * 8 := by grind

-- Signed comparisons
example (x y z : Int64) : x < y → y < z → x < z := by grind
example (x y : Int64) : x ≤ y → y ≤ x → x = y := by grind
/-
example (x y : Int64) : (x < y) ↔ (x.toBitVec.slt y.toBitVec = true) := by grind
-/
/-
example (x y : Int64) : (x ≤ y) ↔ (x.toBitVec.sle y.toBitVec = true) := by grind

-- Word boundary and overflow logic
-/
example : (2^63 - 1 : Int64) + 1 = -(2^63) := by grind
example : (-(2^63) : Int64) - 1 = 2^63 - 1 := by grind

/-
example (x y : Int64) : x < y → x ≠ 2^63 - 1 := by grind
-/
/-
example (x y : Int64) : x < y → y ≠ -(2^63) := by grind


-- Casts and conversions
-/
example (x : UInt64) : (Int64.ofUInt64 x).toUInt64 = x := by grind

-- Commuting of casts
example (x : Int64) : x.toInt16 = x.toInt32.toInt16 := by grind
example (x : Int64) : (x.toInt8).toInt32.toInt8 = x.toInt8 := by grind

-- Division, modulo and shifts
example (x : Int64) : x <<< 0 = x := by grind

-- Boundary tests without modulo for casts to larger types
/-
example (x y z w : Int8) : ((x.toInt16 * y.toInt16) + z.toInt16 + w.toInt16).toInt = (x.toInt * y.toInt) + z.toInt + w.toInt := by
  have := Int8.mul_range x y
  grind [Int16.toInt_add, Int16.toInt_mul, Int8.toInt_toInt16]

-/
/-
example (x y z w : Int16) : ((x.toInt32 * y.toInt32) + z.toInt32 + w.toInt32).toInt = (x.toInt * y.toInt) + z.toInt + w.toInt := by
  have := Int16.mul_range x y
  grind [Int32.toInt_add, Int32.toInt_mul, Int16.toInt_toInt32]

-/
/-
example (x y z w : Int32) : ((x.toInt64 * y.toInt64) + z.toInt64 + w.toInt64).toInt = (x.toInt * y.toInt) + z.toInt + w.toInt := by
  have := Int32.mul_range x y
  grind [Int64.toInt_add, Int64.toInt_mul, Int32.toInt_toInt64]

-- Complex bitwise and sign logic tests
-/
example (x : Int64) : (~~~(~~~x)) = x := by grind
example (x y : Int64) : x - y = x + ~~~y + 1 := by grind

example (x : Int64) : x <<< 1 = x + x := by grind

/-
example (x y : Int64) :
  ((x ^^^ y).toInt < 0) ↔ (x.toInt < 0 ∧ y.toInt ≥ 0) ∨ (x.toInt ≥ 0 ∧ y.toInt < 0) := by
  change ((x.toBitVec ^^^ y.toBitVec).toInt < 0) ↔
    (x.toBitVec.toInt < 0 ∧ y.toBitVec.toInt ≥ 0) ∨ (x.toBitVec.toInt ≥ 0 ∧ y.toBitVec.toInt < 0)
  grind [BitVec.toInt_lt_zero_iff_msb]
-/
