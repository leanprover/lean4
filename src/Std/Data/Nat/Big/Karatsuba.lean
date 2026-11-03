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
public import Std.Data.Nat.Big.Div

/-! Correctness of Karatsuba multiplication. -/

namespace ByteArray

public theorem getElem!_extract' (b : ByteArray) (s e i : Nat) :
    (b.extract s e)[i]! = if i < min e b.size - s then b[s + i]! else 0 := by
  by_cases h : i < min e b.size - s
  · rw [ite_eq_left h, getElem!_pos (b.extract s e) i (by rw [size_extract]; exact h),
      getElem!_pos b (s + i) (by omega), getElem_extract]
  · rw [ite_eq_right h, getElem!_neg (b.extract s e) i (by rw [size_extract]; exact h)]; rfl

public theorem getElem!_append' (a b : ByteArray) (i : Nat) :
    (a ++ b)[i]! = if i < a.size then a[i]! else b[i - a.size]! := by
  by_cases h : i < a.size
  · rw [ite_eq_left h, getElem!_pos (a ++ b) i (by rw [size_append]; omega), getElem!_pos a i h,
      getElem_append_left h]
  · rw [ite_eq_right h]
    by_cases h' : i < (a ++ b).size
    · rw [getElem!_pos (a ++ b) i h', getElem!_pos b (i - a.size) (by rw [size_append] at h'; omega),
        getElem_append_right (by omega)]
    · rw [getElem!_neg (a ++ b) i h', getElem!_neg b (i - a.size) (by rw [size_append] at h'; omega)]

public theorem getElem!_copySlice (src : ByteArray) (so : Nat) (dst : ByteArray) (dO len : Nat)
    (h1 : so + len ≤ src.size) (h2 : dO + len ≤ dst.size) (i : Nat) :
    (src.copySlice so dst dO len)[i]! =
      if dO ≤ i ∧ i < dO + len then src[so + (i - dO)]! else dst[i]! := by
  rw [copySlice_eq_append, getElem!_append', getElem!_append', getElem!_extract', getElem!_extract',
    getElem!_extract']
  simp only [size_data, size_append, size_extract]
  have e1 : min dO dst.size = dO := by omega
  have e2 : min (so + len) src.size = so + len := by omega
  have e3 : min len (src.size - so) = len := by omega
  simp only [e1, e2, e3, Nat.sub_zero, Nat.min_self, Nat.zero_add, Nat.add_sub_cancel_left]
  by_cases hA : i < dO
  · rw [ite_eq_left (show i < dO + len by omega), ite_eq_left hA, ite_eq_right (show ¬(dO ≤ i ∧ i < dO + len) by omega)]
    rw [ite_eq_left hA]
  · by_cases hB : i < dO + len
    · rw [ite_eq_left hB, ite_eq_right hA, ite_eq_left (show i - dO < len by omega), ite_eq_left ⟨by omega, hB⟩]
    · rw [ite_eq_right hB, ite_eq_right (show ¬(dO ≤ i ∧ i < dO + len) by omega)]
      by_cases hC : i - (dO + len) < dst.size - (dO + len)
      · rw [ite_eq_left hC, show dO + len + (i - (dO + len)) = i by omega]
      · rw [ite_eq_right hC, getElem!_neg dst i (by omega)]; rfl

end ByteArray

namespace Nat.Big

public theorem Mag.digit_extractDigits (a : Mag) (lo hi h1 h2) (p : Nat) :
    (extractDigits a lo hi h1 h2).digit p =
      if p < hi.toNat - lo.toNat then a.digit (lo.toNat + p) else 0 := by
  have := maxBytes_lt; have := a.n_le
  have hs : min (hi.toNat * 4) a.bytes.size - lo.toNat * 4 = (hi.toNat - lo.toNat) * 4 := by
    rw [← a.n_mul_four]; omega
  simp only [Mag.digit, extractDigits, ByteArray.readU32, ByteArray.getElem!_extract',
    shiftLeft_toNat lo (by omega), shiftLeft_toNat hi (by omega), hs]
  by_cases hp : p < hi.toNat - lo.toNat
  · have q0 : p * 4 < (hi.toNat - lo.toNat) * 4 := by omega
    have q1 : p * 4 + 1 < (hi.toNat - lo.toNat) * 4 := by omega
    have q2 : p * 4 + 2 < (hi.toNat - lo.toNat) * 4 := by omega
    have q3 : p * 4 + 3 < (hi.toNat - lo.toNat) * 4 := by omega
    simp only [q0, q1, q2, q3, hp, ite_true,
      show lo.toNat * 4 + p * 4 = (lo.toNat + p) * 4 by omega,
      show lo.toNat * 4 + (p * 4 + 1) = (lo.toNat + p) * 4 + 1 by omega,
      show lo.toNat * 4 + (p * 4 + 2) = (lo.toNat + p) * 4 + 2 by omega,
      show lo.toNat * 4 + (p * 4 + 3) = (lo.toNat + p) * 4 + 3 by omega]
  · have q0 : ¬ p * 4 < (hi.toNat - lo.toNat) * 4 := by omega
    have q1 : ¬ p * 4 + 1 < (hi.toNat - lo.toNat) * 4 := by omega
    have q2 : ¬ p * 4 + 2 < (hi.toNat - lo.toNat) * 4 := by omega
    have q3 : ¬ p * 4 + 3 < (hi.toNat - lo.toNat) * 4 := by omega
    simp only [q0, q1, q2, q3, hp, ite_false]
    rfl

public theorem Mag.valUpTo_extractDigits (a : Mag) (lo hi h1 h2) (k : Nat) (hk : k ≤ hi.toNat - lo.toNat) :
    (extractDigits a lo hi h1 h2).valUpTo k = a.valFrom lo.toNat k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Mag.valUpTo, ih (by omega), Mag.digit_extractDigits, ite_eq_left (by omega), Mag.valFrom]

public theorem Mag.val_extractDigits (a : Mag) (lo hi h1 h2) :
    (extractDigits a lo hi h1 h2).val = a.valFrom lo.toNat (hi.toNat - lo.toNat) := by
  rw [Mag.val, n_extractDigits, Mag.valUpTo_extractDigits _ _ _ _ _ _ (Nat.le_refl _)]

public theorem Mag.n_le_of_val_lt (x : Mag) (hx : x.IsNorm) (k : Nat) (h : x.val < 2 ^ (32 * k)) :
    x.n ≤ k := by
  rcases Nat.eq_zero_or_pos x.n with h0 | h0
  · omega
  · have := x.pow_le_val hx h0
    have : 2 ^ (32 * (x.n - 1)) < 2 ^ (32 * k) := Nat.lt_of_le_of_lt this h
    have := (Nat.pow_lt_pow_iff_right (by omega)).mp this
    omega

public theorem Mag.valFrom_zero (a : Mag) (k : Nat) : a.valFrom 0 k = a.valUpTo k := by
  have := a.valUpTo_add 0 k
  simp only [Nat.zero_add, Nat.mul_zero, Nat.pow_zero, Nat.one_mul] at this
  rw [this, show a.valUpTo 0 = 0 from rfl, Nat.zero_add]

public theorem Mag.val_eq_valUpTo_add_valFrom (a : Mag) (m : Nat) (hm : m ≤ a.n) :
    a.val = a.valUpTo m + 2 ^ (32 * m) * a.valFrom m (a.n - m) := by
  rw [Mag.val, ← Mag.valUpTo_add, show m + (a.n - m) = a.n by omega]

/-- A slice is the value of the digits it covers. -/
public theorem val_slice (a : Mag) (lo hi : USize) (h : lo.toNat ≤ min hi.toNat a.n) :
    (slice a lo hi).val = a.valFrom lo.toNat (min hi.toNat a.n - lo.toNat) ∧
      (slice a lo hi).IsNorm := by
  have hc := (clampHi a hi).2
  unfold slice
  dsimp only
  split
  · next h' =>
    have := USize.le_iff_toNat_le.mp h'
    rw [show min hi.toNat a.n - lo.toNat = 0 by omega]
    exact ⟨rfl, Mag.isNorm_empty⟩
  · next h' =>
    refine ⟨?_, Mag.isNorm_normalize _⟩
    rw [Mag.val_normalize, Mag.val_extractDigits, hc]


public theorem Mag.digit_of_shifted (a S : Mag) (k : Nat) (_hfit : (a.n + k) * 4 ≤ maxBytes)
    (hS : S.bytes = a.bytes.copySlice 0 (ByteArray.replicate ((a.n + k) * 4) 0) (k * 4) (a.n * 4))
    (p : Nat) : S.digit p = if k ≤ p ∧ p < k + a.n then a.digit (p - k) else 0 := by
  have hsz := a.n_mul_four
  simp only [Mag.digit, hS, ByteArray.readU32]
  rw [ByteArray.getElem!_copySlice _ _ _ _ _ (by omega) (by rw [size_replicate]; omega),
    ByteArray.getElem!_copySlice _ _ _ _ _ (by omega) (by rw [size_replicate]; omega),
    ByteArray.getElem!_copySlice _ _ _ _ _ (by omega) (by rw [size_replicate]; omega),
    ByteArray.getElem!_copySlice _ _ _ _ _ (by omega) (by rw [size_replicate]; omega)]
  by_cases hp : k ≤ p ∧ p < k + a.n
  · have q0 : k * 4 ≤ p * 4 ∧ p * 4 < k * 4 + a.n * 4 := by omega
    have q1 : k * 4 ≤ p * 4 + 1 ∧ p * 4 + 1 < k * 4 + a.n * 4 := by omega
    have q2 : k * 4 ≤ p * 4 + 2 ∧ p * 4 + 2 < k * 4 + a.n * 4 := by omega
    have q3 : k * 4 ≤ p * 4 + 3 ∧ p * 4 + 3 < k * 4 + a.n * 4 := by omega
    simp only [q0, q1, q2, q3, hp, and_self, ite_true,
      show 0 + (p * 4 - k * 4) = (p - k) * 4 by omega,
      show 0 + (p * 4 + 1 - k * 4) = (p - k) * 4 + 1 by omega,
      show 0 + (p * 4 + 2 - k * 4) = (p - k) * 4 + 2 by omega,
      show 0 + (p * 4 + 3 - k * 4) = (p - k) * 4 + 3 by omega]
  · have q0 : ¬ (k * 4 ≤ p * 4 ∧ p * 4 < k * 4 + a.n * 4) := by omega
    have q1 : ¬ (k * 4 ≤ p * 4 + 1 ∧ p * 4 + 1 < k * 4 + a.n * 4) := by omega
    have q2 : ¬ (k * 4 ≤ p * 4 + 2 ∧ p * 4 + 2 < k * 4 + a.n * 4) := by omega
    have q3 : ¬ (k * 4 ≤ p * 4 + 3 ∧ p * 4 + 3 < k * 4 + a.n * 4) := by omega
    simp only [q0, q1, q2, q3, hp, ite_false, Mag.getElem!_replicate]
    rfl

public theorem Mag.val_of_shifted (a S : Mag) (k : Nat) (hfit : (a.n + k) * 4 ≤ maxBytes)
    (hS : S.bytes = a.bytes.copySlice 0 (ByteArray.replicate ((a.n + k) * 4) 0) (k * 4) (a.n * 4)) :
    S.n = a.n + k ∧ S.val = a.val * 2 ^ (32 * k) := by
  have hsz := a.n_mul_four
  have hn : S.n = a.n + k := by
    have h := S.n_mul_four
    rw [hS, ByteArray.copySlice_eq_append] at h
    simp only [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_data, size_replicate] at h
    omega
  have hd := Mag.digit_of_shifted a S k hfit hS
  refine ⟨hn, ?_⟩
  have hfrom : ∀ i, i ≤ a.n → S.valFrom k i = a.valUpTo i := by
    intro i hi
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [Mag.valFrom, ih (by omega), Mag.valUpTo, hd, ite_eq_left (by omega), show k + i - k = i by omega]
  have hlow : S.valUpTo k = 0 := by
    rw [Mag.valUpTo_eq_of_zero S 0 k (Nat.zero_le _) (fun p _ hp => by rw [hd, ite_eq_right (by omega)])]
    rfl
  rw [Mag.val, hn, Nat.add_comm, Mag.valUpTo_add, hlow, hfrom a.n (Nat.le_refl _), Nat.zero_add,
    Nat.mul_comm]
  rfl

public theorem val_shiftDigits (a : Mag) (k : USize) (h : (a.n + k.toNat) * 4 ≤ maxBytes) :
    (shiftDigits a k).val = a.val * 2 ^ (32 * k.toNat) ∧ (shiftDigits a k).n ≤ a.n + k.toNat := by
  unfold shiftDigits
  split
  · next h0 =>
    have : a.n = 0 := by have := a.usize_toNat; simp at h0; rw [h0] at this; simpa using this.symm
    have hv : a.val = 0 := by rw [Mag.val, this]; rfl
    exact ⟨by rw [hv, Nat.zero_mul], by omega⟩
  · dsimp only
    have := maxBytes_lt
    have hk : (a.usize + k).toNat = a.n + k.toNat := by
      rw [toNat_add_of_lt_size (by rw [a.usize_toNat]; omega), a.usize_toNat]
    constructor
    · refine (Mag.val_of_shifted a _ k.toNat h ?_).2
      simp only [Mag.zeros, hk, Mag.shiftLeft_toNat k (by omega),
        Mag.shiftLeft_toNat a.usize (by rw [a.usize_toNat]; omega), a.usize_toNat]
    · refine Nat.le_of_eq (Mag.val_of_shifted a _ k.toNat h ?_).1
      simp only [Mag.zeros, hk, Mag.shiftLeft_toNat k (by omega),
        Mag.shiftLeft_toNat a.usize (by rw [a.usize_toNat]; omega), a.usize_toNat]

public theorem mul_lt_pow32 (x y m n : Nat) (hx : x < 2 ^ (32 * m)) (hy : y < 2 ^ (32 * n)) :
    x * y < 2 ^ (32 * (m + n)) := by
  rw [Nat.mul_add, Nat.pow_add]
  calc x * y ≤ x * (2 ^ (32 * n) - 1) := Nat.mul_le_mul_left _ (by omega)
    _ < 2 ^ (32 * m) * 2 ^ (32 * n) := by
      have h1 : x * (2 ^ (32 * n) - 1) ≤ (2 ^ (32 * m) - 1) * (2 ^ (32 * n) - 1) :=
        Nat.mul_le_mul_right _ (by omega)
      have h2 : (2 ^ (32 * m) - 1) * (2 ^ (32 * n) - 1) < 2 ^ (32 * m) * 2 ^ (32 * n) := by
        have := Nat.two_pow_pos (32 * m); have := Nat.two_pow_pos (32 * n)
        calc (2 ^ (32 * m) - 1) * (2 ^ (32 * n) - 1) ≤ (2 ^ (32 * m) - 1) * 2 ^ (32 * n) :=
              Nat.mul_le_mul_left _ (by omega)
          _ < 2 ^ (32 * m) * 2 ^ (32 * n) := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      omega

/-- A normalized product has at most as many digits as its factors together. -/
public theorem n_le_of_mul (P x y : Mag) (hP : P.IsNorm) (hv : P.val = x.val * y.val) : P.n ≤ x.n + y.n :=
  P.n_le_of_val_lt hP _ (by rw [hv]; exact mul_lt_pow32 _ _ _ _ x.val_lt y.val_lt)

/-- Karatsuba multiplication computes the product unless it exceeds `maxBytes`. -/
public theorem val_mul (a b : Mag) (ha : a.IsNorm) (hb : b.IsNorm) (h : (a.n + b.n + 1) * 4 ≤ maxBytes) :
    (mul a b).val = a.val * b.val ∧ (mul a b).IsNorm := by
  fun_induction mul a b
  · rename_i a b _ ih
    obtain ⟨h1, h2⟩ := ih hb ha (by omega)
    exact ⟨by rw [h1, Nat.mul_comm], h2⟩
  · exact val_mulBasecase _ _ (by omega)
  · rename_i a b _ _ hla hlb h1 h2 m hm a0 a1 ha0 ha1 hbm ih2 ih1
    have e48 : (48 : USize).toNat = 48 := by
      rcases System.Platform.numBits_eq with h | h <;> simp [USize.toNat_ofNat, h]
    rw [e48] at h2
    have hbm' : b.n ≤ m.toNat := by have := USize.le_iff_toNat_le.mp hbm; omega
    obtain ⟨va0, na0⟩ : a0.val = a.valUpTo m.toNat ∧ a0.IsNorm := by
      have := val_slice a 0 m (by simp)
      rwa [USize.toNat_zero, Nat.sub_zero, show min m.toNat a.n = m.toNat by omega,
        Mag.valFrom_zero] at this
    obtain ⟨va1, na1⟩ : a1.val = a.valFrom m.toNat (a.n - m.toNat) ∧ a1.IsNorm := by
      have := val_slice a m a.usize (by omega)
      rwa [show min a.usize.toNat a.n = a.n by omega] at this
    have hsplit := a.val_eq_valUpTo_add_valFrom m.toNat (by omega)
    rw [← va0, ← va1] at hsplit
    have sa0 : a0.n ≤ m.toNat := by have := ha0.1; simp at this; exact this
    have sa1 : a1.n ≤ a.n - m.toNat := ha1.2
    obtain ⟨vP1, nP1⟩ := ih2 na1 hb (by omega)
    obtain ⟨vP0, nP0⟩ := ih1 na0 hb (by omega)
    have sP1 := n_le_of_mul _ _ _ nP1 vP1
    have sP0 := n_le_of_mul _ _ _ nP0 vP0
    obtain ⟨vS, sS⟩ := val_shiftDigits (mul a1 b) m (by omega)
    obtain ⟨vR, nR⟩ := val_add (shiftDigits (mul a1 b) m) (mul a0 b) (by omega)
    refine ⟨?_, nR⟩
    rw [vR, vS, vP1, vP0, hsplit]
    generalize 2 ^ (32 * m.toNat) = X
    grind
  · rename_i a b _ _ hla hlb h1 h2 m hm a0 a1 ha0 ha1 hbm b0 b1 hb0 hb1 z0 z2 z1 ih3 ih2 ih1
    have e48 : (48 : USize).toNat = 48 := by
      rcases System.Platform.numBits_eq with h | h <;> simp [USize.toNat_ofNat, h]
    rw [e48] at h2
    have hbm' : m.toNat < b.n := by have := not_le_toNat hbm; omega
    have hm2 : (m <<< 1).toNat = 2 * m.toNat := by
      have h1' : (1 : USize).toNat % System.Platform.numBits = 1 := by
        rcases System.Platform.numBits_eq with h | h <;> simp [h]
      have := maxBytes_lt; have := a.n_le
      rw [USize.toNat_shiftLeft, h1', Nat.shiftLeft_eq, ← USize.size_eq_two_pow,
        Nat.mod_eq_of_lt (by omega)]
      omega
    obtain ⟨va0, na0⟩ : a0.val = a.valUpTo m.toNat ∧ a0.IsNorm := by
      have := val_slice a 0 m (by simp)
      rwa [USize.toNat_zero, Nat.sub_zero, show min m.toNat a.n = m.toNat by omega,
        Mag.valFrom_zero] at this
    obtain ⟨va1, na1⟩ : a1.val = a.valFrom m.toNat (a.n - m.toNat) ∧ a1.IsNorm := by
      have := val_slice a m a.usize (by omega)
      rwa [show min a.usize.toNat a.n = a.n by omega] at this
    obtain ⟨vb0, nb0⟩ : b0.val = b.valUpTo m.toNat ∧ b0.IsNorm := by
      have := val_slice b 0 m (by simp)
      rwa [USize.toNat_zero, Nat.sub_zero, show min m.toNat b.n = m.toNat by omega,
        Mag.valFrom_zero] at this
    obtain ⟨vb1, nb1⟩ : b1.val = b.valFrom m.toNat (b.n - m.toNat) ∧ b1.IsNorm := by
      have := val_slice b m b.usize (by omega)
      rwa [show min b.usize.toNat b.n = b.n by omega] at this
    have hsa := a.val_eq_valUpTo_add_valFrom m.toNat (by omega)
    have hsb := b.val_eq_valUpTo_add_valFrom m.toNat (by omega)
    rw [← va0, ← va1] at hsa
    rw [← vb0, ← vb1] at hsb
    have sa0 : a0.n ≤ m.toNat := by have := ha0.1; simp at this; exact this
    have sa1 : a1.n ≤ a.n - m.toNat := ha1.2
    have sb0 : b0.n ≤ m.toNat := by have := hb0.1; simp at this; exact this
    have sb1 : b1.n ≤ b.n - m.toNat := hb1.2
    obtain ⟨vz0, nz0⟩ : z0.val = a0.val * b0.val ∧ z0.IsNorm := ih3 na0 nb0 (by omega)
    obtain ⟨vz2, nz2⟩ : z2.val = a1.val * b1.val ∧ z2.IsNorm := ih2 na1 nb1 (by omega)
    have sz0 := n_le_of_mul _ _ _ nz0 vz0
    have sz2 := n_le_of_mul _ _ _ nz2 vz2
    obtain ⟨vA, nA⟩ := val_add a0 a1 (by omega)
    obtain ⟨vB, nB⟩ := val_add b0 b1 (by omega)
    have sA := n_add_le a0 a1
    have sB := n_add_le b0 b1
    obtain ⟨vM, nM⟩ := ih1 nA nB (by omega)
    obtain ⟨vD, nD⟩ := val_sub _ _ nM nz0
    obtain ⟨vz1, nz1⟩ : z1.val = (mul (add a0 a1) (add b0 b1)).val - z0.val - z2.val ∧ z1.IsNorm := by
      have := val_sub _ z2 nD nz2
      rw [vD] at this
      exact this
    -- the Karatsuba identity: the middle product is `a0 * b1 + a1 * b0`
    have hz1 : z1.val = a0.val * b1.val + a1.val * b0.val := by
      rw [vz1, vM, vA, vB, vz0, vz2]
      have e : (a0.val + a1.val) * (b0.val + b1.val) =
          a0.val * b0.val + a0.val * b1.val + a1.val * b0.val + a1.val * b1.val := by
        rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
      rw [e]; omega
    have hab : a.val * b.val = z2.val * 2 ^ (32 * (2 * m.toNat)) + z1.val * 2 ^ (32 * m.toNat) +
        z0.val := by
      rw [hz1, vz0, vz2, hsa, hsb, show 32 * (2 * m.toNat) = 32 * m.toNat + 32 * m.toNat by omega,
        Nat.pow_add]
      generalize 2 ^ (32 * m.toNat) = X
      grind
    have habl := mul_lt_pow32 _ _ _ _ a.val_lt b.val_lt
    -- the shifted middle product fits below the full product
    have sz1 : z1.n + m.toNat ≤ a.n + b.n := by
      have : z1.val < 2 ^ (32 * (a.n + b.n - m.toNat)) := by
        have h3 : z1.val * 2 ^ (32 * m.toNat) < 2 ^ (32 * (a.n + b.n - m.toNat)) * 2 ^ (32 * m.toNat) := by
          rw [← Nat.pow_add, show 32 * (a.n + b.n - m.toNat) + 32 * m.toNat = 32 * (a.n + b.n) by omega]
          omega
        exact Nat.lt_of_mul_lt_mul_right h3
      have := z1.n_le_of_val_lt nz1 _ this
      omega
    obtain ⟨vS2, sS2⟩ := val_shiftDigits z2 (m <<< 1) (by rw [hm2]; omega)
    obtain ⟨vS1, sS1⟩ := val_shiftDigits z1 m (by omega)
    rw [hm2] at vS2 sS2
    obtain ⟨vT, nT⟩ := val_add (shiftDigits z2 (m <<< 1)) (shiftDigits z1 m) (by omega)
    have sT : (add (shiftDigits z2 (m <<< 1)) (shiftDigits z1 m)).n ≤ a.n + b.n := by
      refine Nat.le_trans ((add (shiftDigits z2 (m <<< 1)) (shiftDigits z1 m)).n_le_of_val_lt nT _ ?_)
        (Nat.le_refl _)
      rw [vT, vS2, vS1]
      omega
    obtain ⟨vR, nR⟩ := val_add (add (shiftDigits z2 (m <<< 1)) (shiftDigits z1 m)) z0 (by omega)
    refine ⟨?_, nR⟩
    rw [vR, vT, vS2, vS1, hab]

end Nat.Big
