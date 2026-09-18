
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
example (x y : UInt64) : x + y - y = x := by grind
example (x y : UInt64) : (x + y) * 0 = 0 := by grind
example (x : UInt64) : x - x = 0 := by grind
example (x : UInt64) : x * 1 = x := by grind
example (x y : UInt64) : y ≤ x → (x - y) + y = x := by grind
example (x y : UInt64) : (x * y) - (y * x) = 0 := by grind

-- Bitwise operations
example (x : UInt64) : x &&& 0 = 0 := by grind
example (x : UInt64) : x ||| 0 = x := by grind
example (x : UInt64) : x ^^^ 0 = x := by grind
example (x : UInt64) : x ^^^ x = 0 := by grind
example (x : UInt64) : x &&& x = x := by grind
example (x : UInt64) : x ||| x = x := by grind
example (x : UInt64) : ~~~(~~~x) = x := by grind

-- Shifts
example (x : UInt64) : x <<< 1 = x + x := by grind

-- Unsigned comparisons
example (x y z : UInt64) : x < y → y < z → x < z := by grind
example (x y : UInt64) : x ≤ y → y ≤ x → x = y := by grind
example (x y : UInt64) : (x < y) ↔ (x.toBitVec < y.toBitVec) := by grind
example (x y : UInt64) : (x ≤ y) ↔ (x.toBitVec ≤ y.toBitVec) := by grind

-- Word boundary and overflow logic
example : (18446744073709551615 : UInt64) + 1 = 0 := by grind
example : (0 : UInt64) - 1 = 18446744073709551615 := by grind
example (x y : UInt64) : (x + y) < x ↔ x.toBitVec + y.toBitVec < x.toBitVec := by grind

example (x y : UInt64) : x < y → y ≠ 0 := by grind

-- Non-ring variable constraints (sum of products unsigned interpretation)
example (x y z w : UInt64) : ((x * y) + (z * w)).toNat = ((x.toNat * y.toNat) + (z.toNat * w.toNat)) % 2^64 := by
  grind [BitVec.toNat_mul, Nat.add_mod, Nat.mul_mod]

-- Division, modulo and shifts
example (x : UInt64) : x >>> 0 = x := by grind
example (x : UInt64) : x <<< 0 = x := by grind
example (x : UInt64) : x / 1 = x := by grind
example (x : UInt64) : x % 1 = 0 := by grind
/-
example (x y z w : UInt32) : ((x.toUInt64 * y.toUInt64) + z.toUInt64 + w.toUInt64).toNat = (x.toNat * y.toNat) + z.toNat + w.toNat := by
  have := Nat.mul_le_mul (UInt32.toNat_le_max x) (UInt32.toNat_le_max y)
  grind

-/
/-
example (x y z w : UInt16) : ((x.toUInt32 * y.toUInt32) + z.toUInt32 + w.toUInt32).toNat = (x.toNat * y.toNat) + z.toNat + w.toNat := by
  have := Nat.mul_le_mul (UInt16.toNat_le_max x) (UInt16.toNat_le_max y)
  grind

-/
/-
example (x y z w : UInt8) : ((x.toUInt16 * y.toUInt16) + z.toUInt16 + w.toUInt16).toNat = (x.toNat * y.toNat) + z.toNat + w.toNat := by
  have := Nat.mul_le_mul (UInt8.toNat_le_max x) (UInt8.toNat_le_max y)
  grind



-/
example (x : UInt64) : (~~~(~~~x)) = x := by grind

example (x : UInt64) : x <<< 1 = x + x := by grind

example (mask a b : UInt64) (hmask : mask = 0 ∨ mask = UInt64.ofNat (2^64 - 1)) :
  ((mask &&& a) ||| (~~~mask &&& b)) = if mask = UInt64.ofNat (2^64 - 1) then a else b := by
  apply UInt64.eq_of_toBitVec_eq
  simp [UInt64.toBitVec_and, UInt64.toBitVec_or, UInt64.toBitVec_not]
  have h : 18446744073709551615#64 = BitVec.allOnes 64 := rfl
  rcases hmask with rfl | rfl
  · change (0#64 &&& a.toBitVec) ||| (~~~(0#64) &&& b.toBitVec) = b.toBitVec
    simp [BitVec.not_zero]
    rw [h, BitVec.allOnes_and]
  · change (18446744073709551615#64 &&& a.toBitVec) ||| (~~~(18446744073709551615#64) &&& b.toBitVec) = a.toBitVec
    rw [h, BitVec.allOnes_and]
    grind
