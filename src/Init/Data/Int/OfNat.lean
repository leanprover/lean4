/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Init.GrindInstances.ToInt
public import Init.Data.Nat.Div.Basic
import Init.ByCases
import Init.Data.Int.DivMod.Lemmas
import Init.Data.Int.LemmasAux
import Init.Data.Int.Pow
import Init.Omega

public section

namespace Nat.ToInt

theorem ofNat_toNat (a : Int) : (NatCast.natCast a.toNat : Int) = if a ≤ 0 then 0 else a := by simp [Int.max_def]

theorem toNat_nonneg (x : Nat) : (-1:Int) * (NatCast.natCast x) ≤ 0 := by simp

theorem natCast_ofNat (n : Nat) : (NatCast.natCast (OfNat.ofNat n : Nat) : Int) = OfNat.ofNat n := by rfl

theorem of_eq {a b : Nat} {a' b' : Int}
    (h₁ : NatCast.natCast a = a') (h₂ : NatCast.natCast b = b') : a = b → a' = b' := by
  intro h; replace h := congrArg (NatCast.natCast (R := Int)) h
  rw [h₁, h₂] at h; assumption

theorem of_diseq {a b : Nat} {a' b' : Int}
    (h₁ : NatCast.natCast a = a') (h₂ : NatCast.natCast b = b') : a ≠ b → a' ≠ b' := by
  intro hne h; rw [← h₁, ← h₂] at h
  replace h := Int.ofNat_inj.mp h; contradiction

theorem of_dvd (d a : Nat) (d' a' : Int)
    (h₁ : NatCast.natCast d = d') (h₂ : NatCast.natCast a = a') : d ∣ a → d' ∣ a' := by
  simp [← h₁, ←h₂, Int.ofNat_dvd]

theorem of_le {a b : Nat} {a' b' : Int}
    (h₁ : NatCast.natCast a = a') (h₂ : NatCast.natCast b = b') : a ≤ b → a' ≤ b' := by
  intro h; replace h := Int.ofNat_le |>.mpr h
  rw [← h₁, ← h₂]; assumption

theorem of_not_le {a b : Nat} {a' b' : Int}
    (h₁ : NatCast.natCast a = a') (h₂ : NatCast.natCast b = b') : ¬ (a ≤ b) → b' + 1 ≤ a' := by
  intro h; rw [← Int.ofNat_le] at h
  rw [← h₁, ← h₂]; show (↑b + 1 : Int) ≤ a; omega

theorem add_congr {a b : Nat} {a' b' : Int}
    (h₁ : NatCast.natCast a = a') (h₂ : NatCast.natCast b = b') : NatCast.natCast (a + b) = a' + b' := by
  simp_all [Int.natCast_add]

theorem mul_congr {a b : Nat} {a' b' : Int}
    (h₁ : NatCast.natCast a = a') (h₂ : NatCast.natCast b = b') : NatCast.natCast (a * b) = a' * b' := by
  simp_all [Int.natCast_mul]

theorem sub_congr {a b : Nat} {a' b' : Int}
    (h₁ : NatCast.natCast a = a') (h₂ : NatCast.natCast b = b') : NatCast.natCast (a - b) = if b' + (-1)*a' ≤ 0 then a' - b' else 0 := by
  rw [Int.neg_mul, ← Int.sub_eq_add_neg, Int.one_mul]
  split
  next h =>
    have h := Int.le_of_sub_nonpos h
    simp [← h₁, ← h₂, Int.ofNat_le] at h
    simp [Int.ofNat_sub h]
    rw [← h₁, ← h₂]
  next h =>
    have : ¬ (↑b : Int) ≤ ↑a := by
      intro h
      replace h := Int.sub_nonpos_of_le h
      simp [h₁, h₂] at h
      contradiction
    rw [Int.ofNat_le] at this
    simp [Lean.Omega.Int.ofNat_sub_eq_zero this]

theorem pow_congr {a : Nat} (k : Nat) (a' : Int)
    (h₁ : NatCast.natCast a = a') : NatCast.natCast (a ^ k) = a' ^ k := by
  simp_all [Int.natCast_pow]

theorem div_congr {a b : Nat} {a' b' : Int}
    (h₁ : NatCast.natCast a = a') (h₂ : NatCast.natCast b = b') : NatCast.natCast (a / b) = a' / b' := by
  simp_all [Int.natCast_ediv]

theorem mod_congr {a b : Nat} {a' b' : Int}
    (h₁ : NatCast.natCast a = a') (h₂ : NatCast.natCast b = b') : NatCast.natCast (a % b) = a' % b' := by
  simp_all [Int.natCast_emod]

theorem finVal {n : Nat} {a : Fin n} {a' : Int}
    (h₁ : Lean.Grind.ToInt.toInt a = a') : NatCast.natCast (a.val) = a' := by
  rw [← h₁, Lean.Grind.ToInt.toInt, Lean.Grind.instToIntFinCoOfNatIntCast]

theorem eq_eq {a b : Nat} {a' b' : Int}
    (h₁ : NatCast.natCast a = a') (h₂ : NatCast.natCast b = b') : (a = b) = (a' = b') := by
  simp [← h₁, ←h₂]; constructor
  next => intro; subst a; rfl
  next => simp [Int.natCast_inj]

theorem lt_eq {a b : Nat} {a' b' : Int}
    (h₁ : NatCast.natCast a = a') (h₂ : NatCast.natCast b = b') : (a < b) = (a' < b') := by
  simp only [← h₁, ← h₂, Int.ofNat_lt]

theorem le_eq {a b : Nat} {a' b' : Int}
    (h₁ : NatCast.natCast a = a') (h₂ : NatCast.natCast b = b') : (a ≤ b) = (a' ≤ b') := by
  simp only [← h₁, ← h₂, Int.ofNat_le]

end Nat.ToInt

namespace Int.Nonneg

@[expose] def num_cert (a : Int) : Bool := a ≥ 0
theorem num (a : Int) : num_cert a → a ≥ 0 := by simp [num_cert]
theorem add (a b : Int) (h₁ : a ≥ 0) (h₂ : b ≥ 0) : a + b ≥ 0 := by exact Int.add_nonneg h₁ h₂
theorem mul (a b : Int) (h₁ : a ≥ 0) (h₂ : b ≥ 0) : a * b ≥ 0 := by exact Int.mul_nonneg h₁ h₂
theorem div (a b : Int) (h₁ : a ≥ 0) (h₂ : b ≥ 0) : a / b ≥ 0 := by exact Int.ediv_nonneg h₁ h₂
theorem pow (a : Int) (k : Nat) (h₁ : a ≥ 0) : a ^ k ≥ 0 := by exact Int.pow_nonneg h₁
theorem mod (a b : Int) (h₁ : a ≥ 0) : a % b ≥ 0 := by
  by_cases b = 0
  next => simp [*]
  next h => exact emod_nonneg a h
theorem natCast (a : Nat) : (NatCast.natCast a : Int) ≥ 0 := by simp
theorem toPoly (e : Int) : e ≥ 0 → -1 * e ≤ 0 := by omega

end Int.Nonneg
