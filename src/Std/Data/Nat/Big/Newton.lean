/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
module

prelude
public import Init.Data.Nat.Big
public import Init.Data.Nat
public import Init.Data.String
public import Init.Data.List
public import Init.Data.Array
public import Init.Data.UInt
public import Init.Data.Int
public import Init.Data.ByteArray
public import Init.Data.Fin
import Init.Grind
import Init.GrindInstances
import Init.Omega
import all Init.Data.ByteArray.Basic
import all Init.Data.ByteArray.Extra
import all Init.Data.UInt.Log2
import all Init.Data.Fin.Log2
public import Std.Data.Nat.Big.Karatsuba

/-! Correctness of Newton division and `divMod`. -/

namespace Nat.Big

public theorem val_one : (ofUInt64 1).val = 1 ∧ (ofUInt64 1).IsNorm := by
  have := val_ofUInt64 1
  simpa using this

public theorem div_mod_of_eq {a b Q R : Nat} (hb : 0 < b) (h : a = Q * b + R) (hR : R < b) :
    a / b = Q ∧ a % b = R := by
  subst h
  refine ⟨?_, ?_⟩
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt hR, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hR]

public theorem cmp_gt_iff (x y : Mag) (hx : x.IsNorm) (hy : y.IsNorm) :
    (cmp x y == .gt) = true ↔ y.val < x.val := by
  rw [cmp_spec x y hx hy]
  constructor
  · intro h; exact Nat.compare_eq_gt.mp (by simpa using h)
  · intro h; simp [Nat.compare_eq_gt.mpr h]

public theorem cmp_ne_lt_iff (x y : Mag) (hx : x.IsNorm) (hy : y.IsNorm) :
    (cmp x y != .lt) = true ↔ y.val ≤ x.val := by
  rw [cmp_spec x y hx hy]
  constructor
  · intro h
    have : compare x.val y.val ≠ .lt := by simpa using h
    exact Nat.not_lt.mp (fun h' => this (Nat.compare_eq_lt.mpr h'))
  · intro h
    have : compare x.val y.val ≠ .lt := fun h' => Nat.not_lt.mpr h (Nat.compare_eq_lt.mp h')
    simpa using this

public theorem newtonDown_spec (a b : Mag) (ha : a.IsNorm) (hb : b.IsNorm) (hfit : (a.n + 1) * 4 ≤ maxBytes)
    (hbpos : 0 < b.val) (fuel : Nat) (q qb : Mag) (hq : q.IsNorm) (hqb : qb.IsNorm)
    (hinv : qb.val = q.val * b.val) (hgt : a.val < qb.val) :
    (newtonDown a b fuel q qb).1.val = a.val / b.val ∧
      (newtonDown a b fuel q qb).2.val = a.val % b.val ∧
      (newtonDown a b fuel q qb).1.IsNorm ∧ (newtonDown a b fuel q qb).2.IsNorm := by
  obtain ⟨v1, n1⟩ := val_one
  fun_induction newtonDown a b fuel q qb
  · exact divModBasecase_spec a b ha hb hfit
  · rename_i q qb q' qb' hc fuel ih
    have hq1 : 1 ≤ q.val := Nat.pos_of_ne_zero (fun h0 => by rw [h0, Nat.zero_mul] at hinv; omega)
    obtain ⟨vq', nq'⟩ : q'.val = q.val - 1 ∧ q'.IsNorm := by
      have := val_sub q (ofUInt64 1) hq n1; rwa [v1] at this
    obtain ⟨vqb', nqb'⟩ : qb'.val = qb.val - b.val ∧ qb'.IsNorm := val_sub qb b hqb hb
    have hgt' : a.val < qb'.val := (cmp_gt_iff _ _ nqb' ha).mp hc
    exact ih nq' nqb' (by rw [vqb', vq', hinv, Nat.sub_mul, Nat.one_mul]) hgt'
  · rename_i _ q qb q' qb' hc
    have hq1 : 1 ≤ q.val := Nat.pos_of_ne_zero (fun h0 => by rw [h0, Nat.zero_mul] at hinv; omega)
    obtain ⟨vq', nq'⟩ : q'.val = q.val - 1 ∧ q'.IsNorm := by
      have := val_sub q (ofUInt64 1) hq n1; rwa [v1] at this
    obtain ⟨vqb', nqb'⟩ : qb'.val = qb.val - b.val ∧ qb'.IsNorm := val_sub qb b hqb hb
    have hle : qb'.val ≤ a.val := Nat.not_lt.mp (fun h => hc ((cmp_gt_iff _ _ nqb' ha).mpr h))
    obtain ⟨vr, nr⟩ := val_sub a qb' ha nqb'
    have hmul : qb'.val = (q.val - 1) * b.val := by rw [vqb', hinv, Nat.sub_mul, Nat.one_mul]
    have hq : q.val * b.val = (q.val - 1) * b.val + b.val := by
      rw [Nat.sub_mul, Nat.one_mul]
      have : b.val ≤ q.val * b.val := Nat.le_mul_of_pos_left _ hq1
      omega
    obtain ⟨hd, hm⟩ := div_mod_of_eq (a := a.val) (b := b.val) (Q := q.val - 1)
      (R := a.val - qb'.val) hbpos (by omega) (by omega)
    exact ⟨by rw [vq', hd], by rw [vr, hm], nq', nr⟩

public theorem newtonUp_spec (a b : Mag) (ha : a.IsNorm) (hb : b.IsNorm) (hfit : (a.n + 3) * 4 ≤ maxBytes)
    (hbpos : 0 < b.val) (fuel : Nat) (q r : Mag) (hq : q.IsNorm) (hr : r.IsNorm)
    (hinv : q.val * b.val + r.val = a.val) :
    (newtonUp a b fuel q r).1.val = a.val / b.val ∧ (newtonUp a b fuel q r).2.val = a.val % b.val ∧
      (newtonUp a b fuel q r).1.IsNorm ∧ (newtonUp a b fuel q r).2.IsNorm := by
  obtain ⟨v1, n1⟩ := val_one
  have s1 : (ofUInt64 1).n ≤ 1 := (ofUInt64 1).n_le_of_val_lt n1 1 (by rw [v1]; decide)
  fun_induction newtonUp a b fuel q r
  · exact divModBasecase_spec a b ha hb (by omega)
  · rename_i q r hc fuel ih
    have hge : b.val ≤ r.val := (cmp_ne_lt_iff _ _ hr hb).mp hc
    have hqa : q.val ≤ a.val := by
      have : q.val ≤ q.val * b.val := Nat.le_mul_of_pos_right _ hbpos
      omega
    have sq : q.n ≤ a.n := q.n_le_of_val_lt hq _ (Nat.lt_of_le_of_lt hqa a.val_lt)
    obtain ⟨vq', nq'⟩ := val_add q (ofUInt64 1) (by omega)
    obtain ⟨vr', nr'⟩ := val_sub r b hr hb
    refine ih nq' nr' ?_
    rw [vq', vr', v1, Nat.add_mul, Nat.one_mul]
    omega
  · rename_i q r hc
    have hlt : r.val < b.val := Nat.not_le.mp (fun h => hc ((cmp_ne_lt_iff _ _ hr hb).mpr h))
    obtain ⟨hd, hm⟩ := div_mod_of_eq hbpos hinv.symm hlt
    exact ⟨hd.symm, hm.symm, hq, hr⟩

public theorem newtonFinish_spec (a b q : Mag) (ha : a.IsNorm) (hb : b.IsNorm) (hq : q.IsNorm)
    (hfit : (a.n + 3) * 4 ≤ maxBytes) (hbpos : 0 < b.val) :
    (newtonFinish a b q).1.val = a.val / b.val ∧ (newtonFinish a b q).2.val = a.val % b.val ∧
      (newtonFinish a b q).1.IsNorm ∧ (newtonFinish a b q).2.IsNorm := by
  unfold newtonFinish
  split
  · next hs =>
    obtain ⟨vqb, nqb⟩ := val_mul q b hq hb (by omega)
    dsimp only
    split
    · next hc =>
      exact newtonDown_spec a b ha hb (by omega) hbpos 64 q _ hq nqb vqb
        ((cmp_gt_iff _ _ nqb ha).mp hc)
    · next hc =>
      have hle : (mul q b).val ≤ a.val :=
        Nat.not_lt.mp (fun h => hc ((cmp_gt_iff _ _ nqb ha).mpr h))
      obtain ⟨vr, nr⟩ := val_sub a (mul q b) ha nqb
      exact newtonUp_spec a b ha hb hfit hbpos 64 q _ hq nr (by rw [vr, ← vqb]; omega)
  · exact divModBasecase_spec a b ha hb (by omega)

public theorem divModNewton_spec (a b : Mag) (ha : a.IsNorm) (hb : b.IsNorm)
    (hfit : (a.n + 3) * 4 ≤ maxBytes) (hbpos : 0 < b.val) :
    (divModNewton a b).1.val = a.val / b.val ∧ (divModNewton a b).2.val = a.val % b.val ∧
      (divModNewton a b).1.IsNorm ∧ (divModNewton a b).2.IsNorm := by
  unfold divModNewton
  exact newtonFinish_spec a b _ ha hb (val_shiftRight _ _).2 hfit hbpos

public theorem bitLen_eq_zero (b : Mag) (h : b.n = 0) : bitLen b = 0 := by
  have : b.usize = 0 := USize.toNat_inj.mp (by rw [b.usize_toNat, h]; rfl)
  unfold bitLen
  simp [this]

/-- `divMod` computes quotient and remainder (with `a / 0 = 0` and `a % 0 = a`). -/
public theorem divMod_spec (a b : Mag) (ha : a.IsNorm) (hb : b.IsNorm) (hfit : (a.n + 3) * 4 ≤ maxBytes) :
    (divMod a b).1.val = a.val / b.val ∧ (divMod a b).2.val = a.val % b.val ∧
      (divMod a b).1.IsNorm ∧ (divMod a b).2.IsNorm := by
  unfold divMod
  dsimp only
  split
  · next h =>
    have hbn : 0 < b.n := by
      rcases Nat.eq_zero_or_pos b.n with h0 | h0
      · rw [bitLen_eq_zero b h0] at h
        have e : (24576 : USize).toNat = 24576 := by
          rcases System.Platform.numBits_eq with h | h <;> simp [USize.toNat_ofNat, h]
        simp at h
        have := congrArg USize.toNat h.1
        rw [e] at this
        simp at this
      · exact h0
    exact divModNewton_spec a b ha hb hfit
      (Nat.lt_of_lt_of_le (Nat.two_pow_pos _) (b.pow_le_val hb hbn))
  · exact divModBasecase_spec a b ha hb (by omega)

end Nat.Big
