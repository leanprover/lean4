
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

-- Algebraic & Modulo Arithmetic Tests
example (x y z : Fin n) [NeZero n] :
  (x + y + z).val = (x.val + y.val + z.val) % n := by grind

example (x y z : Fin n) [NeZero n] :
  (x * y * z).val = (x.val * y.val * z.val) % n := by grind

example (x y : Fin (2^16)) :
  (x - y).val = if y ≤ x then x.val - y.val else x.val + 2^16 - y.val := by grind

example (x : Fin n) :
  (-x).val = (n - x.val) % n := by grind

-- Bound & Range Propagation Tests
example (x : Fin n) : x.val < n := by grind

example (x y : Fin n) : (x + y).val < n := by grind

-- Conditional (ITE) Tests
example (c : Prop) [Decidable c] (x y z : Fin n) [NeZero n] :
  (if c then x + z else y + z).val = (if c then x.val + z.val else y.val + z.val) % n := by grind

-- Equality & Zero Tests
example [NeZero n] (x : Fin n) : x = 0 ↔ x.val = 0 := by grind

example [NeZero n] (x : Fin n) (h : x ≠ 0) : x.val ≠ 0 := by grind

example [NeZero n] (x y : Fin n) : x = y ↔ x.val = y.val := by grind

-- log2 and intCast Tests
/-
example (x : Fin n) : (x.log2).val = Nat.log2 x.val := by grind

open Fin.IntCast in
-/
/-
example [NeZero n] (i : Int) : ((i : Fin n)).val = (i % n).toNat := by grind

-- Boolean / Bitwise operations
-/
example (x y : Fin n) : (x &&& y).val = x.val &&& y.val := by grind
example (x y : Fin n) : (x ||| y).val = (x.val ||| y.val) % n := by grind
example (x y : Fin n) : (x ^^^ y).val = (x.val ^^^ y.val) % n := by grind

-- Challenging Carry Propagation test case
example (x y : Fin (2^64)) (c : Fin 2) :
    let s := x.val + y.val + c.val
    let l : Fin (2^64) := Fin.ofNat (2^64) s
    let h : Fin 2 := Fin.ofNat 2 (s / 2^64)
    s = l.val + 2^64 * h.val := by
  grind

-- Shift and complement tests for Fin
example (x : Fin n) (k : Fin n) : (x <<< k).val = (x.val <<< k.val) % n := by grind
example (x : Fin n) (k : Fin n) : (x >>> k).val = x.val >>> k.val := by grind

example (x : Fin n) : (~~~x).val = n - 1 - x.val := by grind
