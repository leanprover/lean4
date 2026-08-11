/-
Copyright (c) 2026 Andres Erbsen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Erbsen, Leonardo de Moura
-/
module
prelude
import Init.Grind.Attr
public import Init.Data.Fin.Lemmas
public import Init.Data.Fin.Bitwise
public import Init.Grind.ToInt
public section

/-!
Homomorphism rules for `Fin` used by the `grind` tactic. The embedding is
`Lean.Grind.ToNat.toNat`, defined as `Fin.val`, so the translated facts are stated over
the marker applications tracked by `grind`'s linear integer arithmetic solver to implement
model construction and mbtc.
-/

namespace Lean.Grind

instance : ToNat (Fin n) where
  toNat n := n.val

namespace Fin
open ToNat

/-! Translations of `=`, `≤`, and `<`. -/

@[grind hom] theorem eq_iff_toNat_eq {n : Nat} (a b : Fin n) : a = b ↔ toNat a = toNat b :=
  ⟨Fin.val_eq_of_eq, Fin.eq_of_val_eq⟩

@[grind hom] theorem le_iff_toNat_le {n : Nat} (a b : Fin n) : a ≤ b ↔ toNat a ≤ toNat b :=
  Fin.le_def

@[grind hom] theorem lt_iff_toNat_lt {n : Nat} (a b : Fin n) : a < b ↔ toNat a < toNat b :=
  Fin.lt_def

/-! Value rules. -/

@[grind hom] theorem toNat_add {n : Nat} (a b : Fin n) : toNat (a + b) = (toNat a + toNat b) % n :=
  Fin.val_add a b

@[grind hom] theorem toNat_mul {n : Nat} (a b : Fin n) : toNat (a * b) = toNat a * toNat b % n :=
  Fin.val_mul a b

@[grind hom] theorem toNat_sub {n : Nat} (a b : Fin n) : toNat (a - b) = (n - toNat b + toNat a) % n :=
  Fin.val_sub a b

@[grind hom] theorem toNat_mod {n : Nat} (a m : Fin n) : toNat (a % m) = toNat a % toNat m :=
  Fin.val_mod a m

@[grind hom] theorem toNat_div {n : Nat} (a b : Fin n) : toNat (a / b) = toNat a / toNat b :=
  Fin.div_val a b

@[grind hom] theorem toNat_succ {n : Nat} (j : Fin n) : toNat j.succ = toNat j + 1 :=
  Fin.val_succ j

@[grind hom] theorem toNat_neg {n : Nat} (a : Fin n) : toNat (-a) = (n - toNat a) % n :=
  Fin.val_neg' a

@[grind hom] theorem toNat_and {n : Nat} (a b : Fin n) : toNat (a &&& b) = toNat a &&& toNat b :=
  Fin.and_val a b

@[grind hom] theorem toNat_or {n : Nat} (a b : Fin n) : toNat (a ||| b) = (toNat a ||| toNat b) % n :=
  Fin.or_val a b

@[grind hom] theorem toNat_xor {n : Nat} (a b : Fin n) : toNat (a ^^^ b) = (toNat a ^^^ toNat b) % n :=
  Fin.xor_val a b

@[grind hom] theorem toNat_shiftLeft {n : Nat} (a b : Fin n) : toNat (a <<< b) = toNat a <<< toNat b % n :=
  Fin.shiftLeft_val a b

@[grind hom] theorem toNat_shiftRight {n : Nat} (a b : Fin n) : toNat (a >>> b) = toNat a >>> toNat b :=
  Fin.shiftRight_val a b

@[grind hom] theorem toNat_ite {n : Nat} (c : Prop) [Decidable c] (x y : Fin n) : toNat (if c then x else y) = if c then toNat x else toNat y := by
  split <;> rfl

@[grind hom] theorem toNat_ofNat (n : Nat) [NeZero n] (a : Nat) : toNat (OfNat.ofNat a : Fin n) = a % n := by
  show (OfNat.ofNat a : Fin n).val = a % n
  dsimp [OfNat.ofNat]

@[grind hom] theorem toNat_mk {n : Nat} (a : Nat) (h : a < n) : toNat (Fin.mk a h) = a :=
  rfl

/-! Fold the projection spelling into the embedding. -/

@[grind hom] theorem val_eq_toNat {n : Nat} (a : Fin n) : a.val = toNat a := rfl

/-! Range fact, instantiated by `grind` for the marker applications it internalizes. -/

@[grind hom_pred] theorem toNat_lt {n : Nat} (a : Fin n) : toNat a < n := a.isLt

end Fin
end Lean.Grind
