
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

/-!
# Tests for Nat → Int cast and relation homomorphisms in `grind`.

Verifies that `Int.natCast_add`, `Int.natCast_mul`, `Int.natCast_pow`, `Int.natCast_shiftLeft`,
`Int.natCast_inj`, `Int.ofNat_le`, and `Int.ofNat_lt` (registered in `Init/Data/Int/Lemmas.lean`)
are automatically picked up by `grind` across mixed arithmetic.
-/

example (a b c d s : Nat)
    (h_add : ((a + b : Nat) : Int) = 100)
    (h_mul : ((c * d : Nat) : Int) = 50)
    (h_pow : ((a ^ 2 : Nat) : Int) = 25)
    (h_shift : ((c <<< s : Nat) : Int) = 16)
    (h_le : ((a : Int) ≤ (b : Int)))
    (h_lt : ((c : Int) < (d : Int))) :
    (a : Int) + (b : Int) = 100 ∧
    (c : Int) * (d : Int) = 50 ∧
    (a : Int) ^ 2 = 25 ∧
    (c : Int) <<< s = 16 ∧
    a ≤ b ∧
    c < d := by
  grind

example (x y : Nat) (h : ((x : Int) = (y : Int))) : x = y := by
  grind
