/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Init.Data.Zero
import all Init.Data.Zero
public import Init.Grind.Ring.Basic
public import Init.GrindInstances.ToInt
import all Init.GrindInstances.ToInt
public import Init.Data.Fin.Lemmas

public section

namespace Lean.Grind

namespace Fin

-- TODO: we should replace this at runtime with either repeated squaring,
-- or a GMP accelerated function.
@[expose]
def npow [NeZero n] (x : Fin n) (y : Nat) : Fin n := npowRec y x

instance [NeZero n] : HPow (Fin n) Nat (Fin n) where
  hPow := Fin.npow

instance [NeZero n] : Pow (Fin n) Nat where
  pow := Fin.npow

@[simp] theorem pow_zero [NeZero n] (a : Fin n) : a ^ 0 = 1 := rfl
@[simp] theorem pow_succ [NeZero n] (a : Fin n) (n : Nat) : a ^ (n+1) = a ^ n * a := rfl

theorem add_assoc (a b c : Fin n) : a + b + c = a + (b + c) := by
  cases a; cases b; cases c; simp [Fin.add_def, Nat.add_assoc]

theorem add_comm (a b : Fin n) : a + b = b + a := by
  cases a; cases b; simp [Fin.add_def, Nat.add_comm]

theorem add_zero [NeZero n] (a : Fin n) : a + 0 = a := by
  cases a; simp [Fin.add_def]
  next h => rw [Nat.mod_eq_of_lt h]

theorem neg_add_cancel [NeZero n] (a : Fin n) : -a + a = 0 := by
  cases a; simp [Fin.add_def, Fin.neg_def]
  next h => rw [Nat.sub_add_cancel (Nat.le_of_lt h), Nat.mod_self]

theorem mul_assoc (a b c : Fin n) : a * b * c = a * (b * c) := by
  cases a; cases b; cases c; simp [Fin.mul_def, Nat.mul_assoc]

theorem mul_comm (a b : Fin n) : a * b = b * a := by
  cases a; cases b; simp [Fin.mul_def, Nat.mul_comm]

theorem zero_mul [NeZero n] (a : Fin n) : 0 * a = 0 := by
  cases a; simp [Fin.mul_def]

theorem mul_one [NeZero n] (a : Fin n) : a * 1 = a := by
  cases a; simp [Fin.mul_def, OfNat.ofNat]
  next h => rw [Nat.mod_eq_of_lt h]

theorem left_distrib (a b c : Fin n) : a * (b + c) = a * b + a * c := by
  cases a; cases b; cases c; simp [Fin.mul_def, Fin.add_def, Nat.left_distrib]

theorem ofNat_succ [NeZero n] (a : Nat) : OfNat.ofNat (α := Fin n) (a+1) = OfNat.ofNat a + 1 := by
  simp [OfNat.ofNat, Fin.add_def, Fin.ofNat]

theorem sub_eq_add_neg [NeZero n] (a b : Fin n) : a - b = a + -b := by
  cases a; cases b; simp [Fin.neg_def, Fin.sub_def, Fin.add_def, Nat.add_comm]

private theorem neg_neg [NeZero n] (a : Fin n) : - - a = a := by
  obtain ⟨a, h⟩ := a; simp [Fin.neg_def]
  cases a; simp; next a =>
   rw [Nat.self_sub_mod n (a+1)]
   have : NeZero (n - (a + 1)) := ⟨by omega⟩
   rw [Nat.self_sub_mod, Nat.sub_sub_eq_min, Nat.min_eq_right (Nat.le_of_lt h)]

theorem _root_.Nat.sub_sub_right (a : Nat) {b c : Nat} (h : c ≤ b) : a - (b - c) = a + c - b := by omega

theorem neg_mul [NeZero n] (a b : Fin n) : (-a) * b = -(a * b) := by
  rcases a with ⟨a, ha⟩; rcases b with ⟨b, hb⟩
  ext
  simp only [Fin.neg_def, Fin.mul_def, Nat.mod_mul_mod]
  rw [Nat.sub_mul]
  rw [Nat.mod_eq_mod_iff]
  match b with
  | 0 => refine ⟨1, 0, by simp⟩
  | b+1 =>
    refine ⟨a*(b+1)/n, b, ?_⟩
    rw [Nat.mod_def, Nat.mul_add_one, Nat.mul_comm _ n, Nat.mul_comm b n]
    have : n * (a * (b + 1) / n) ≤ a * (b + 1) := Nat.mul_div_le (a * (b + 1)) n
    have := Nat.lt_mul_div_succ (a * (b + 1)) (show 0 < n by omega)
    rw [Nat.mul_add_one n] at this
    have : a * (b + 1) ≤ n * b + n := by
      rw [Nat.mul_add_one]
      have := Nat.mul_le_mul_right b ha
      rw [Nat.succ_mul] at this
      omega
    omega

open Fin.NatCast Fin.IntCast in
theorem intCast_neg [NeZero n] (i : Int) : Int.cast (R := Fin n) (-i) = - Int.cast (R := Fin n) i := by
  simp [Int.cast, IntCast.intCast, Fin.intCast]
  split <;> split <;> try omega
  next h₁ h₂ => simp [Int.le_antisymm h₁ h₂, Fin.neg_def]
  next => simp [Fin.neg_neg]

open Fin.NatCast Fin.IntCast in
instance (n : Nat) [NeZero n] : CommRing (Fin n) where
  nsmul := ⟨fun k i => (k : Fin n) * i⟩
  zsmul := ⟨fun k i => (k : Fin n) * i⟩
  natCast := Fin.NatCast.instNatCast n
  intCast := Fin.IntCast.instIntCast n
  add_assoc := Fin.add_assoc
  add_comm := Fin.add_comm
  add_zero := Fin.add_zero
  neg_add_cancel := Fin.neg_add_cancel
  mul_assoc := Fin.mul_assoc
  mul_comm := Fin.mul_comm
  mul_one := Fin.mul_one
  left_distrib := Fin.left_distrib
  zero_mul := Fin.zero_mul
  pow_zero _ := by rfl
  pow_succ _ _ := by rfl
  ofNat_succ := Fin.ofNat_succ
  sub_eq_add_neg := Fin.sub_eq_add_neg
  intCast_neg := Fin.intCast_neg
  neg_zsmul i a := by
    change (((-i) : Int) : Fin n)* a = - ((i : Fin n) * a)
    simp [intCast_neg, neg_mul]
  zsmul_natCast_eq_nsmul _ _ := rfl

instance (n : Nat) [NeZero n] : IsCharP (Fin n) n := IsCharP.mk' _ _
  (ofNat_eq_zero_iff := fun x => by
    change Fin.ofNat _ _ = Fin.ofNat _ _ ↔ _
    simp only [Fin.ofNat]
    simp only [Nat.zero_mod]
    simp only [Fin.mk.injEq])

example [NeZero n] : ToInt.Neg (Fin n) (.co 0 n) := inferInstance
example [NeZero n] : ToInt.Sub (Fin n) (.co 0 n) := inferInstance

instance [i : NeZero n] : ToInt.Pow (Fin n) (.co 0 n) where
  toInt_pow x k := by
    induction k with
    | zero =>
      match n, i with
      | 1, _ => rfl
      | (n + 2), _ =>
        simp [IntInterval.wrap, Int.sub_zero, Int.add_zero]
        rw [Int.emod_eq_of_lt] <;> omega
    | succ k ih =>
      rw [pow_succ, ToInt.Mul.toInt_mul, ih, ← ToInt.wrap_toInt,
        ← IntInterval.wrap_mul (by simp), Int.pow_succ, ToInt.wrap_toInt]

end Fin

end Lean.Grind
