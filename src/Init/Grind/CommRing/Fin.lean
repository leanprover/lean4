/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
import Init.Grind.CommRing.Basic
import Init.Data.Fin.Lemmas

namespace Lean.Grind

instance (n : Nat) [NeZero n] : NatCast (Fin n) where
  natCast a := Fin.ofNat' n a

instance (n : Nat) [NeZero n] : Neg (Fin n) where
  neg a := 0 - a

theorem Fin.neg_def [NeZero n] (a : Fin n) : -a = 0 - a := by
  rfl

def Fin.intCast [NeZero n] (a : Int) : Fin n :=
  if a >= 0 then
    Fin.ofNat' n a.natAbs
  else
    - Fin.ofNat' n a.natAbs

instance (n : Nat) [NeZero n] : IntCast (Fin n) where
  intCast := Fin.intCast

-- TODO: we should replace this at runtime with either repeated squaring,
-- or a GMP accelerated function.
def Fin.npow [NeZero n] (x : Fin n) (y : Nat) : Fin n := npowRec y x

instance [NeZero n] : HPow (Fin n) Nat (Fin n) where
  hPow := Fin.npow

theorem Fin.add_assoc (a b c : Fin n) : a + b + c = a + (b + c) := by
  cases a; cases b; cases c; simp [Fin.add_def, Nat.add_assoc]

theorem Fin.add_comm (a b : Fin n) : a + b = b + a := by
  cases a; cases b; simp [Fin.add_def, Nat.add_comm]

theorem Fin.add_zero [NeZero n] (a : Fin n) : a + 0 = a := by
  cases a; simp [Fin.add_def]
  next h => rw [Nat.mod_eq_of_lt h]

theorem Fin.neg_add_cancel [NeZero n] (a : Fin n) : -a + a = 0 := by
  cases a; simp [Fin.add_def, Fin.neg_def, Fin.sub_def]
  next h => rw [Nat.sub_add_cancel (Nat.le_of_lt h), Nat.mod_self]

theorem Fin.mul_assoc (a b c : Fin n) : a * b * c = a * (b * c) := by
  cases a; cases b; cases c; simp [Fin.mul_def, Nat.mul_assoc]

theorem Fin.mul_comm (a b : Fin n) : a * b = b * a := by
  cases a; cases b; simp [Fin.mul_def, Nat.mul_comm]

theorem Fin.zero_mul [NeZero n] (a : Fin n) : 0 * a = 0 := by
  cases a; simp [Fin.mul_def]

theorem Fin.mul_one [NeZero n] (a : Fin n) : a * 1 = a := by
  cases a; simp [Fin.mul_def, OfNat.ofNat]
  next h => rw [Nat.mod_eq_of_lt h]

theorem Fin.left_distrib (a b c : Fin n) : a * (b + c) = a * b + a * c := by
  cases a; cases b; cases c; simp [Fin.mul_def, Fin.add_def, Nat.left_distrib]

theorem Fin.ofNat_succ [NeZero n] (a : Nat) : OfNat.ofNat (α := Fin n) (a+1) = OfNat.ofNat a + 1 := by
  simp [OfNat.ofNat, Fin.add_def, Fin.ofNat']

theorem Fin.sub_eq_add_neg [NeZero n] (a b : Fin n) : a - b = a + -b := by
  cases a; cases b; simp [Fin.neg_def, Fin.sub_def, Fin.add_def, Nat.add_comm]

private theorem Fin.neg_neg [NeZero n] (a : Fin n) : - - a = a := by
  cases a; simp [Fin.neg_def, Fin.sub_def];
  next a h => cases a; simp; next a =>
   rw [Nat.self_sub_mod n (a+1)]
   have : NeZero (n - (a + 1)) := ⟨by omega⟩
   rw [Nat.self_sub_mod, Nat.sub_sub_eq_min, Nat.min_eq_right (Nat.le_of_lt h)]

theorem Fin.intCast_neg [NeZero n] (i : Int) : Int.cast (R := Fin n) (-i) = - Int.cast (R := Fin n) i := by
  simp [Int.cast, IntCast.intCast, Fin.intCast]; split <;> split <;> try omega
  next h₁ h₂ => simp [Int.le_antisymm h₁ h₂, Fin.neg_def]
  next => simp [Fin.neg_neg]

instance (n : Nat) [NeZero n] : CommRing (Fin n) where
  add_assoc := Fin.add_assoc
  add_comm := Fin.add_comm
  add_zero := Fin.add_zero
  neg_add_cancel := Fin.neg_add_cancel
  mul_assoc := Fin.mul_assoc
  mul_comm := Fin.mul_comm
  mul_one := Fin.mul_one
  left_distrib := Fin.left_distrib
  zero_mul := Fin.zero_mul
  pow_zero _ := rfl
  pow_succ _ _ := rfl
  ofNat_succ := Fin.ofNat_succ
  sub_eq_add_neg := Fin.sub_eq_add_neg
  intCast_neg := Fin.intCast_neg

instance (n : Nat) [NeZero n] : IsCharP (Fin n) n where
  ofNat_eq_zero_iff x := by simp only [OfNat.ofNat, Fin.ofNat']; simp

end Lean.Grind
