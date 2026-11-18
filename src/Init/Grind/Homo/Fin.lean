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
public import Init.Data.Fin.Log2
import all Init.Data.Fin.Log2
public import Init.Data.Int.DivMod.Lemmas
import Init.Omega
public section

/-!
Homomorphism rules for `Fin` used by the `grind` tactic.
The injection function is `Fin.val`.
-/

attribute [grind hom]
  Fin.val_add Fin.val_mul Fin.val_sub Fin.val_mod Fin.val_succ Fin.val_neg'
  Fin.div_val Fin.and_val Fin.or_val Fin.xor_val Fin.shiftLeft_val Fin.shiftRight_val
  Fin.le_def Fin.lt_def

@[grind hom] theorem Lean.Grind.Fin.eq_iff_val_eq {n : Nat} (a b : Fin n) : a = b ↔ a.val = b.val :=
  ⟨Fin.val_eq_of_eq, Fin.eq_of_val_eq⟩

@[grind hom] theorem Lean.Grind.Fin.val_ite {n : Nat} (c : Prop) [Decidable c] (x y : Fin n) :
    (if c then x else y).val = if c then x.val else y.val := by
  split <;> rfl

@[grind hom] theorem Lean.Grind.Fin.val_OfNat_ofNat (n : Nat) [NeZero n] (a : Nat) : (OfNat.ofNat a : Fin n).val = a % n := by
  dsimp [OfNat.ofNat]

@[grind hom] theorem Lean.Grind.Fin.val_log2 {n : Nat} (a : Fin n) : a.log2.val = a.val.log2 := by
  simp [Fin.log2]

open Fin.NatCast in
@[grind hom] theorem Lean.Grind.Fin.val_natCast (n : Nat) [NeZero n] (a : Nat) :
    (NatCast.natCast a : Fin n).val = a % n := rfl

open Fin.IntCast in
@[grind hom] theorem Lean.Grind.Fin.val_intCast (n : Nat) [NeZero n] (i : Int) :
    (IntCast.intCast i : Fin n).val = (i % n).toNat := by
  have hn : n ≠ 0 := NeZero.ne n
  change (Fin.intCast i : Fin n).val = _
  unfold Fin.intCast
  split
  next h => rw [Fin.val_ofNat, Int.emod_natAbs_of_nonneg h]
  next h =>
    have h : i < 0 := by omega
    change (n - i.natAbs % n) % n = _
    rw [Int.emod_natAbs_of_neg h hn]
    have h₁ := Int.emod_nonneg i (b := n) (by omega)
    have h₂ := Int.emod_lt_of_pos i (b := n) (by omega)
    split
    next hd => simp [Int.emod_eq_zero_of_dvd hd]
    next hd =>
      have : i % n ≠ 0 := fun h => hd (Int.dvd_of_emod_eq_zero h)
      rw [Nat.mod_eq_of_lt (by omega)]
      omega

/-! Homomorphism predicate: the range fact for `Fin.val`, instantiated by `grind` for
the terms it internalizes. -/

attribute [grind hom_pred] Fin.isLt
