
import Init.Grind
import Init.Data.BitVec
import Init.Data.Fin.Lemmas
import Init.Data.Fin.Bitwise
import Init.Data.UInt
import Init.Data.SInt.Basic

import Init.Grind
import Init.Data.BitVec
import Init.Data.Int.Bitwise.Lemmas

-- Shim for prototype names
abbrev BitVec.unsigned {w} (x : BitVec w) : Int := Int.ofNat x.toNat
abbrev BitVec.signed {w} (x : BitVec w) := x.toInt

-- Missing instances in standard Lean
def Fin.lnot {n : Nat} (a : Fin n) : Fin n := ⟨n - 1 - a.val, by have := a.isLt; omega⟩
instance {n : Nat} : Complement (Fin n) where complement := Fin.lnot

@[grind hom] theorem Fin.val_lnot {n : Nat} (a : Fin n) : (~~~a).val = n - 1 - a.val := rfl

-- Compatibility lemmas for ported tests
/-
theorem BitVec.toNat_eq_unsigned {w} (x : BitVec w) : x.toNat = x.unsigned := rfl



@[grind_homo] theorem natCast_toNat {w} (x : BitVec w) : (x.toNat : Int) = x.unsigned := rfl

-/
example (α : Type) (l1 l2 : List α) (x : α) (a b : BitVec 32)
  (h_len : (l1 ++ l2).length = (a + b).toNat)
  (h_a : a < b) :
  (((l1.take a.toNat).reverse ++ (l2.drop b.toNat)).concat x).length ≤ (a + b).toNat + 1 := by
  grind
