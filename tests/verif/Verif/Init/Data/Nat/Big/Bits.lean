module

import all Init.Data.ByteArray.Basic
import all Init.Data.ByteArray.Extra
import all Init.Data.UInt.Log2
import all Init.Data.Fin.Log2
public import Verif.Init.Data.Nat.Big.Newton

/-! Correctness of the bit queries `log2`, `trailingZeros` and `low64`. -/

namespace Nat.Big

public theorem Mag.n_mul_32_lt (a : Mag) : a.n * 32 < USize.size := by
  have := maxBytes_lt; have := a.n_le; omega

public theorem shl5_toNat (i : USize) (h : i.toNat * 32 < USize.size) : (i <<< 5).toNat = i.toNat * 32 := by
  have e : (5 : USize).toNat % System.Platform.numBits = 5 := by
    rcases System.Platform.numBits_eq with e | e <;> simp [e]
  rw [USize.toNat_shiftLeft, e, Nat.shiftLeft_eq, ← USize.size_eq_two_pow, Nat.mod_eq_of_lt (by omega)]

public theorem Mag.val_top (a : Mag) (h : 0 < a.n) :
    a.val = a.valUpTo (a.n - 1) + a.digit (a.n - 1) * 2 ^ (32 * (a.n - 1)) := by
  have e : a.valUpTo (a.n - 1 + 1) =
      a.valUpTo (a.n - 1) + a.digit (a.n - 1) * 2 ^ (32 * (a.n - 1)) := by rw [Mag.valUpTo]
  rw [show a.n - 1 + 1 = a.n by omega] at e
  exact e

/-- `log2` computes `Nat.log2`. -/
public theorem log2_spec (a : Mag) (ha : a.IsNorm) : (log2 a).toNat = Nat.log2 a.val := by
  unfold log2
  dsimp only
  split
  · next h =>
    have : a.n = 0 := by have := a.usize_toNat; rw [h] at this; simpa using this.symm
    rw [Mag.val, this]; rfl
  · next h =>
    have hn : 0 < a.n := by
      have : a.usize.toNat ≠ 0 := fun h' => h (USize.toNat_inj.mp (by simpa using h'))
      rw [a.usize_toNat] at this; omega
    have hp : (a.usize - 1).toNat = a.n - 1 := by rw [toNat_pred (by rw [a.usize_toNat]; omega), a.usize_toNat]
    have hsz := a.n_mul_32_lt
    have htop : a.digit (a.n - 1) ≠ 0 := by
      rcases ha with h' | h'
      · omega
      · exact h'
    have hg : (a.get (a.usize - 1) (by omega)).toNat = a.digit (a.n - 1) := by rw [Mag.get_toNat, hp]
    have hL := Nat.lt_log2_self (n := a.digit (a.n - 1))
    have hL1 := Nat.log2_self_le htop
    have hL3 : Nat.log2 (a.digit (a.n - 1)) < 32 := (Nat.log2_lt htop).mpr (a.digit_lt _)
    rw [toNat_add_of_lt_size (by
        rw [shl5_toNat _ (by rw [hp]; omega), UInt32.toNat_toUSize, UInt32.toNat_log2', hg]; omega),
      shl5_toNat _ (by rw [hp]; omega), UInt32.toNat_toUSize, UInt32.toNat_log2', hg, hp]
    have hv := a.val_top hn
    have hlo := a.valUpTo_lt (a.n - 1)
    have hv0 : a.val ≠ 0 := by
      have : 1 ≤ a.digit (a.n - 1) * 2 ^ (32 * (a.n - 1)) :=
        Nat.mul_pos (Nat.pos_of_ne_zero htop) (Nat.two_pow_pos _)
      omega
    clear hg
    generalize a.digit (a.n - 1) = top at *
    generalize hX : 2 ^ (32 * (a.n - 1)) = X at hv hlo
    generalize Nat.log2 top = L at *
    apply Nat.le_antisymm
    · refine (Nat.le_log2 hv0).mpr ?_
      rw [Nat.pow_add, show (a.n - 1) * 32 = 32 * (a.n - 1) by omega, hX, hv]
      rw [Nat.mul_comm X]
      exact Nat.le_trans (Nat.mul_le_mul_right X hL1) (Nat.le_add_left _ _)
    · refine Nat.le_of_lt_succ ((Nat.log2_lt hv0).mpr ?_)
      rw [Nat.succ_eq_add_one, show (a.n - 1) * 32 + L + 1 = 32 * (a.n - 1) + (L + 1) by omega,
        Nat.pow_add, hX, hv]
      have h1 : top * X + X ≤ 2 ^ (L + 1) * X := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right X hL
      rw [Nat.mul_comm X]
      omega

public theorem ctz32_spec (x : UInt32) (i : USize) (hi) (hx : x ≠ 0) (hlt : x.toNat < 2 ^ (32 - i.toNat)) :
    i.toNat ≤ (ctz32 x i hi).toNat ∧ (ctz32 x i hi).toNat < 32 ∧
      x.toNat.testBit ((ctz32 x i hi).toNat - i.toNat) = true ∧
      ∀ j, j < (ctz32 x i hi).toNat - i.toNat → x.toNat.testBit j = false := by
  have hx' : x.toNat ≠ 0 := fun h => hx (UInt32.toNat_inj.mp (by rw [h]; rfl))
  fun_induction ctz32 x i hi with
  | case1 x i hi h hi32 h32 ih =>
    have hs : (x >>> 1).toNat = x.toNat / 2 := by
      simp [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    have hb : x.toNat % 2 = 0 := by
      have := congrArg UInt32.toNat h.2
      simpa [UInt32.toNat_and] using this
    have hsucc : (i + 1).toNat = i.toNat + 1 := toNat_succ_of_lt_size (by omega)
    have hx2 : x >>> 1 ≠ 0 := fun h0 => hx' (by
      have := congrArg UInt32.toNat h0; rw [hs] at this; simp at this; omega)
    obtain ⟨r1, r2, r3, r4⟩ := ih hx2 (by
      rw [hs, hsucc, show 32 - (i.toNat + 1) = 32 - i.toNat - 1 by omega]
      have : 2 ^ (32 - i.toNat) = 2 ^ (32 - i.toNat - 1) * 2 := by
        rw [← Nat.pow_succ]; congr 1; omega
      omega) (fun h0 => by rw [hs] at h0; omega)
    rw [hsucc, hs] at *
    refine ⟨by omega, r2, ?_, ?_⟩
    · rw [show (ctz32 (x >>> 1) (i + 1) _).toNat - i.toNat =
          (ctz32 (x >>> 1) (i + 1) _).toNat - (i.toNat + 1) + 1 by omega, ← Nat.testBit_div_two]
      exact r3
    · intro j hj
      rcases j with _ | j
      · simp [Nat.testBit_zero, hb]
      · rw [← Nat.testBit_div_two]; exact r4 j (by omega)
  | case2 x i hi h =>
    have hi32 : i.toNat < 32 := by
      rcases Nat.lt_or_ge i.toNat 32 with h' | h'
      · exact h'
      · exfalso
        rw [show 32 - i.toNat = 0 by omega] at hlt
        simp at hlt; exact hx' (by omega)
    have hb : x.toNat % 2 = 1 := by
      have h1 : ¬ x &&& 1 = 0 := fun h0 => h ⟨by
        have e32 : (32 : USize).toNat = 32 := by
          rcases System.Platform.numBits_eq with e | e <;> simp [USize.toNat_ofNat, e]
        exact USize.lt_iff_toNat_lt.mpr (by omega), h0⟩
      have : (x &&& 1).toNat ≠ 0 := fun h0 => h1 (UInt32.toNat_inj.mp (by rw [h0]; rfl))
      simp [UInt32.toNat_and] at this
      omega
    refine ⟨Nat.le_refl _, hi32, ?_, fun j hj => by omega⟩
    simp [Nat.testBit_zero, hb]


public theorem trailingZerosLoop_spec (a : Mag) (hv : a.val ≠ 0) (i : USize) (hi)
    (hz : ∀ p, p < i.toNat → a.digit p = 0) :
    a.val.testBit (trailingZerosLoop a i hi).toNat = true ∧
      ∀ j, j < (trailingZerosLoop a i hi).toNat → a.val.testBit j = false := by
  have hsz := a.n_mul_32_lt
  fun_induction trailingZerosLoop a i hi with
  | case1 i hi h hi' x hx ih =>
    have hsucc : (i + 1).toNat = i.toNat + 1 := toNat_succ_of_lt_size (by omega)
    refine ih (fun p hp => ?_)
    rw [hsucc] at hp
    rcases Nat.lt_or_ge p i.toNat with h' | h'
    · exact hz p h'
    · have : p = i.toNat := by omega
      subst this
      rw [← Mag.get_toNat a i hi']
      have : x = 0 := by simpa using hx
      simp [x] at this
      rw [this]; rfl
  | case2 i hi h hi' x hx =>
    have hx0 : x ≠ 0 := by simpa using hx
    have hxd : x.toNat = a.digit i.toNat := Mag.get_toNat a i hi'
    obtain ⟨-, r2, r3, r4⟩ := ctz32_spec x 0 (by simp) hx0 (by simpa using x.toNat_lt)
    simp only [USize.toNat_zero, Nat.sub_zero] at r3 r4
    have hr : ((i <<< 5) + ctz32 x 0 (by simp)).toNat = i.toNat * 32 + (ctz32 x 0 (by simp)).toNat := by
      rw [toNat_add_of_lt_size (by rw [shl5_toNat _ (by omega)]; omega), shl5_toNat _ (by omega)]
    rw [hr]
    generalize (ctz32 x 0 _).toNat = r at r2 r3 r4 ⊢
    refine ⟨?_, fun j hj => ?_⟩
    · rw [Mag.testBit_val, show (i.toNat * 32 + r) / 32 = i.toNat by omega,
        show (i.toNat * 32 + r) % 32 = r by omega, ← hxd]
      exact r3
    · rw [Mag.testBit_val]
      rcases Nat.lt_or_ge (j / 32) i.toNat with h' | h'
      · rw [hz _ h']; exact Nat.zero_testBit _
      · rw [show j / 32 = i.toNat by omega, ← hxd]
        exact r4 _ (by omega)
  | case3 i hi h =>
    exfalso
    have hle := not_lt_toNat h
    rw [a.usize_toNat] at hle
    apply hv
    rw [Mag.val, Mag.valUpTo_eq_of_zero a 0 a.n (Nat.zero_le _) (fun p _ hp => hz p (by omega))]
    rfl


/-- `trailingZeros` is the index of the lowest set bit. -/
public theorem trailingZeros_spec (a : Mag) (hv : a.val ≠ 0) :
    a.val.testBit (trailingZeros a).toNat = true ∧
      ∀ j, j < (trailingZeros a).toNat → a.val.testBit j = false :=
  trailingZerosLoop_spec a hv 0 _ (fun p hp => by simp at hp)

public theorem low64_word (x y : UInt32) :
    (x.toUInt64 ||| y.toUInt64 <<< 32) = (y.toUInt64 <<< 32) ||| x.toUInt64 :=
  UInt64.or_comm _ _

/-- `low64` is the value modulo `2^64`. -/
public theorem low64_spec (a : Mag) : (low64 a).toNat = a.val % 2 ^ 64 := by
  unfold low64
  rw [low64_word, toNat_window, getOr0_toNat, getOr0_toNat, USize.toNat_zero, USize.toNat_one,
    ← a.val_div_mod 0, ← a.val_div_mod 1, show (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 by rw [← Nat.pow_add],
    Nat.mod_mul]
  simp only [base_eq, Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.mul_one]
  omega

end Nat.Big
