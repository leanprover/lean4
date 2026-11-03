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
public import Std.Data.Nat.Big.Basic
public import Std.Data.Nat.Big.Knuth

/-! Correctness of long division (Knuth's algorithm D). -/

namespace Nat.Big

/-! ## Digit loops -/

public theorem mul1Loop_spec (q : UInt64) (hq : q.toNat < 2 ^ 32) (v : Mag) (n : USize) (hn) (i : USize)
    (k : UInt64) (ms : Mag) (hms hi) (hk : k.toNat < 2 ^ 32)
    (hinv : ms.valUpTo i.toNat + k.toNat * 2 ^ (32 * i.toNat) = q.toNat * v.valUpTo i.toNat) :
    (mul1Loop q v n hn i k ms hms hi).valUpTo (n.toNat + 1) = q.toNat * v.valUpTo n.toNat := by
  fun_induction mul1Loop q v n hn i k ms hms hi with
  | case1 i k ms hms hi h hi' t ih =>
    have hg : (v.get i (by omega)).toNat = v.digit i.toNat := Mag.get_toNat _ _ _
    have hx := v.digit_lt i.toNat
    have hb := mul_step _ _ 0 _ hq hx (by omega) hk
    have ht : t.toNat = q.toNat * v.digit i.toNat + k.toNat := by
      simp only [t, UInt64.toNat_add, UInt64.toNat_mul, UInt32.toNat_toUInt64, hg]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have hcarry : (t >>> 32).toNat = t.toNat / 2 ^ 32 := by
      simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    have hst : t.toUInt32.toNat = t.toNat % 2 ^ 32 := by simp
    apply ih (by rw [hcarry]; omega)
    rw [toNat_succ_of_lt h, Mag.valUpTo_set_succ, hst, hcarry, Mag.valUpTo,
      show 32 * (i.toNat + 1) = 32 * i.toNat + 32 by omega, Nat.pow_add]
    have hdm := Nat.div_add_mod t.toNat (2 ^ 32)
    rw [ht] at hdm ⊢
    generalize (2 : Nat) ^ (32 * i.toNat) = X at *
    grind
  | case2 i k ms hms hi h =>
    have hle := not_lt_toNat h
    have hk32 : k.toUInt32.toNat = k.toNat := by simp; omega
    rw [Mag.valUpTo_set_succ, hk32, show n.toNat = i.toNat by omega, hinv]

public theorem subInPlace_spec (b : Mag) (len off : USize) (hb) (i : USize) (k : UInt64) (u : Mag) (hu hi)
    (hk : k.toNat < 2) (Z₀ : Nat)
    (hinv : u.valUpTo (off.toNat + len.toNat) + b.valUpTo i.toNat * 2 ^ (32 * off.toNat) =
      Z₀ + k.toNat * 2 ^ (32 * (off.toNat + i.toNat))) :
    ∃ k' : Nat, k' < 2 ∧
      (subInPlace b len off hb i k u hu hi).valUpTo (off.toNat + len.toNat) +
          b.valUpTo len.toNat * 2 ^ (32 * off.toNat) =
        Z₀ + k' * 2 ^ (32 * (off.toNat + len.toNat)) := by
  fun_induction subInPlace b len off hb i k u hu hi with
  | case1 i k u hu hi h hi' hoi t ih =>
    have hga : (u.get (off + i) (by omega)).toNat = u.digit (off.toNat + i.toNat) := by
      rw [Mag.get_toNat, hoi]
    have hgb : (b.get i (by omega)).toNat = b.digit i.toNat := Mag.get_toNat _ _ _
    obtain ⟨hs1, hs2⟩ := sub_step (u.get (off + i) (by omega)) (b.get i (by omega)) k hk
    simp only [hga, hgb] at hs1
    apply ih hs2
    have hset := u.valUpTo_set' (off + i) (by omega) t.toUInt32 (off.toNat + len.toNat) _ hoi
      (by omega)
    rw [toNat_succ_of_lt h, Mag.valUpTo, show 32 * (off.toNat + (i.toNat + 1)) =
      32 * off.toNat + 32 * i.toNat + 32 by omega, Nat.pow_add, Nat.pow_add]
    rw [show 32 * (off.toNat + i.toNat) = 32 * off.toNat + 32 * i.toNat by omega, Nat.pow_add]
      at hinv hset
    generalize (2 : Nat) ^ (32 * off.toNat) = Y at *
    generalize (2 : Nat) ^ (32 * i.toNat) = X at *
    have h1 := congrArg (· * (Y * X)) hs1
    simp only [Nat.add_mul] at h1
    grind
  | case2 i k u hu hi h =>
    have hle := not_lt_toNat h
    rw [show i.toNat = len.toNat by omega] at hinv
    exact ⟨k.toNat, hk, hinv⟩

public theorem subInPlace_frame (b : Mag) (len off : USize) (hb) (i : USize) (k : UInt64) (u : Mag) (hu hi)
    (p : Nat) (hp : p < off.toNat + i.toNat ∨ off.toNat + len.toNat ≤ p) :
    (subInPlace b len off hb i k u hu hi).digit p = u.digit p := by
  fun_induction subInPlace b len off hb i k u hu hi with
  | case1 i k u hu hi h hi' hoi t ih =>
    have := toNat_succ_of_lt h
    rw [ih (by omega), Mag.digit_set, ite_eq_right (by rw [hoi]; omega)]
  | case2 => rfl

public theorem add_step3 (x y : UInt32) (k : UInt64) (hk : k.toNat < 2) :
    let t := x.toUInt64 + y.toUInt64 + k
    t.toUInt32.toNat + (t >>> 32).toNat * 2 ^ 32 = x.toNat + y.toNat + k.toNat ∧
      (t >>> 32).toNat < 2 := by
  intro t
  have := x.toNat_lt; have := y.toNat_lt
  have ht : t.toNat = x.toNat + y.toNat + k.toNat := by
    simp only [t, UInt64.toNat_add, UInt32.toNat_toUInt64]
    have : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
    have : (2 : Nat) ^ 32 = 4294967296 := rfl
    omega
  have h1 : (t >>> 32).toNat = t.toNat / 2 ^ 32 := by
    simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  have h2 : t.toUInt32.toNat = t.toNat % 2 ^ 32 := by simp
  rw [h1, h2, ht]
  have : (2 : Nat) ^ 32 = 4294967296 := rfl
  omega

public theorem addInPlace_spec (v : Mag) (len off : USize) (i : USize) (k : UInt64) (u : Mag) (hu hi)
    (hk : k.toNat < 2) (Z₀ L T : Nat) (hL : L = len.toNat) (hT : T = off.toNat + len.toNat)
    (hinv : u.valUpTo T + k.toNat * 2 ^ (32 * (off.toNat + i.toNat)) =
      Z₀ + v.valUpTo i.toNat * 2 ^ (32 * off.toNat)) :
    ∃ k' : Nat, k' < 2 ∧
      (addInPlace v len off i k u hu hi).valUpTo T + k' * 2 ^ (32 * T) =
        Z₀ + v.valUpTo L * 2 ^ (32 * off.toNat) := by
  subst hL hT
  fun_induction addInPlace v len off i k u hu hi with
  | case1 i k u hu hi h hi' hoi t ih =>
    have hga : (u.get (off + i) (by omega)).toNat = u.digit (off.toNat + i.toNat) := by
      rw [Mag.get_toNat, hoi]
    have hgv : (getOr0 v i).toNat = v.digit i.toNat := getOr0_toNat v i
    obtain ⟨hs1, hs2⟩ := add_step3 (getOr0 v i) (u.get (off + i) (by omega)) k hk
    simp only [hga, hgv] at hs1
    apply ih hs2
    have hset := u.valUpTo_set' (off + i) (by omega) t.toUInt32 (off.toNat + len.toNat) _ hoi
      (by omega)
    rw [toNat_succ_of_lt h, Mag.valUpTo, show 32 * (off.toNat + (i.toNat + 1)) =
      32 * off.toNat + 32 * i.toNat + 32 by omega, Nat.pow_add, Nat.pow_add]
    rw [show 32 * (off.toNat + i.toNat) = 32 * off.toNat + 32 * i.toNat by omega, Nat.pow_add]
      at hinv hset
    generalize (2 : Nat) ^ (32 * off.toNat) = Y at *
    generalize (2 : Nat) ^ (32 * i.toNat) = X at *
    have h1 := congrArg (· * (Y * X)) hs1
    simp only [Nat.add_mul] at h1
    grind
  | case2 i k u hu hi h =>
    have hle := not_lt_toNat h
    rw [show i.toNat = len.toNat by omega] at hinv
    exact ⟨k.toNat, hk, hinv⟩

public theorem addInPlace_frame (v : Mag) (len off : USize) (i : USize) (k : UInt64) (u : Mag) (hu hi)
    (p : Nat) (hp : p < off.toNat + i.toNat ∨ off.toNat + len.toNat ≤ p) :
    (addInPlace v len off i k u hu hi).digit p = u.digit p := by
  fun_induction addInPlace v len off i k u hu hi with
  | case1 i k u hu hi h hi' hoi t ih =>
    have := toNat_succ_of_lt h
    rw [ih (by omega), Mag.digit_set, ite_eq_right (by rw [hoi]; omega)]
  | case2 => rfl


/-! ## The trial quotient digit -/

public theorem toNat_window (x y : UInt32) :
    ((x.toUInt64 <<< 32) ||| y.toUInt64).toNat = x.toNat * base + y.toNat := by
  have h := div1_word x.toUInt64 y (by simpa using x.toNat_lt)
  simpa using h

public theorem trial_spec (dn1 dn2 nu x y : UInt32) (k vrest ulow V W : Nat)
    (hV : V = (dn1.toNat * base + dn2.toNat) * base ^ k + vrest) (hvrest : vrest < base ^ k)
    (hW : W = (x.toNat * base + y.toNat) * base ^ (k+1) + nu.toNat * base ^ k + ulow)
    (hulow : ulow < base ^ k) (hnorm : base ≤ 2 * dn1.toNat) (hWV : W < V * base) :
    (recheck (((x.toUInt64 <<< 32) ||| y.toUInt64) / dn1.toUInt64)
        (((x.toUInt64 <<< 32) ||| y.toUInt64) % dn1.toUInt64) dn1.toUInt64 dn2.toUInt64
        nu.toUInt64).toNat < base ∧
      W / V ≤ (recheck (((x.toUInt64 <<< 32) ||| y.toUInt64) / dn1.toUInt64)
        (((x.toUInt64 <<< 32) ||| y.toUInt64) % dn1.toUInt64) dn1.toUInt64 dn2.toUInt64
        nu.toUInt64).toNat ∧
      (recheck (((x.toUInt64 <<< 32) ||| y.toUInt64) / dn1.toUInt64)
        (((x.toUInt64 <<< 32) ||| y.toUInt64) % dn1.toUInt64) dn1.toUInt64 dn2.toUInt64
        nu.toUInt64).toNat ≤ W / V + 1 := by
  have hvtop1 : 1 ≤ dn1.toNat := by simp only [base_eq] at hnorm; omega
  have hd1 : dn1.toNat < base := dn1.toNat_lt_size
  have hd2 : dn2.toNat < base := dn2.toNat_lt_size
  have hnu : nu.toNat < base := nu.toNat_lt_size
  have hpk : 0 < base ^ k := Nat.pow_pos (by simp)
  have hpk1 : 0 < base ^ (k+1) := Nat.pow_pos (by simp)
  have hpow : base ^ (k+1) = base ^ k * base := Nat.pow_succ base k
  have htemp := toNat_window x y
  have hq0 : (((x.toUInt64 <<< 32) ||| y.toUInt64) / dn1.toUInt64).toNat =
      (x.toNat * base + y.toNat) / dn1.toNat := by
    rw [UInt64.toNat_div, htemp, UInt32.toNat_toUInt64]
  have hr0 : (((x.toUInt64 <<< 32) ||| y.toUInt64) % dn1.toUInt64).toNat =
      (x.toNat * base + y.toNat) % dn1.toNat := by
    rw [UInt64.toNat_mod, htemp, UInt32.toNat_toUInt64]
  have hinv0 : x.toNat * base + y.toNat =
      (((x.toUInt64 <<< 32) ||| y.toUInt64) / dn1.toUInt64).toNat * dn1.toNat +
        (((x.toUInt64 <<< 32) ||| y.toUInt64) % dn1.toUInt64).toNat := by
    rw [hq0, hr0]; exact (Nat.div_add_mod' _ _).symm
  have hrlt : (((x.toUInt64 <<< 32) ||| y.toUInt64) % dn1.toUInt64).toNat < base := by
    rw [hr0]; exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega)) (Nat.le_of_lt hd1)
  -- the low part of the divisor stays below one unit of its leading digit
  have hlowV : dn2.toNat * base ^ k + vrest < base ^ (k+1) := by
    have h1 : dn2.toNat * base ^ k ≤ (base - 1) * base ^ k := Nat.mul_le_mul_right _ (by omega)
    have h2 : (base - 1) * base ^ k + base ^ k = base ^ (k+1) := by
      rw [hpow, Nat.sub_mul, Nat.one_mul, Nat.mul_comm (base ^ k) base]
      have : base ^ k ≤ base * base ^ k := Nat.le_mul_of_pos_left _ (by simp)
      omega
    omega
  have hVsplit : V = dn1.toNat * base ^ (k+1) + (dn2.toNat * base ^ k + vrest) := by
    rw [hV, hpow]; grind
  have hVlt : V < (dn1.toNat + 1) * base ^ (k+1) := by
    rw [hVsplit, Nat.add_mul, Nat.one_mul]; omega
  have hlowW : nu.toNat * base ^ k + ulow < base ^ (k+1) := by
    have h1 : nu.toNat * base ^ k ≤ (base - 1) * base ^ k := Nat.mul_le_mul_right _ (by omega)
    have h2 : (base - 1) * base ^ k + base ^ k = base ^ (k+1) := by
      rw [hpow, Nat.sub_mul, Nat.one_mul, Nat.mul_comm (base ^ k) base]
      have : base ^ k ≤ base * base ^ k := Nat.le_mul_of_pos_left _ (by simp)
      omega
    omega
  have hu2bound : x.toNat * base + y.toNat ≤ dn1.toNat * base + (base - 1) := by
    have hge : (x.toNat * base + y.toNat) * base ^ (k+1) ≤ W := by rw [hW]; omega
    have hlt : W < ((dn1.toNat + 1) * base) * base ^ (k+1) := by
      calc W < V * base := hWV
        _ < ((dn1.toNat + 1) * base ^ (k+1)) * base := (Nat.mul_lt_mul_right (by simp)).mpr hVlt
        _ = ((dn1.toNat + 1) * base) * base ^ (k+1) := by grind
    have := Nat.lt_of_mul_lt_mul_right (a := base ^ (k+1)) (Nat.lt_of_le_of_lt hge hlt)
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  -- Theorem A: the initial estimate is not too small
  have hle0 : W / V ≤ (x.toNat * base + y.toNat) / dn1.toNat := by
    have hVd : V / base ^ (k+1) = dn1.toNat := by
      rw [hVsplit, Nat.mul_comm, Nat.mul_add_div hpk1, Nat.div_eq_of_lt hlowV, Nat.add_zero]
    have hUd : W / base ^ (k+1) = x.toNat * base + y.toNat := by
      rw [hW, Nat.add_assoc, Nat.mul_comm, Nat.mul_add_div hpk1, Nat.div_eq_of_lt hlowW, Nat.add_zero]
    have := KnuthD.le_qhat (u := W) (v := V) (P := base ^ (k+1)) hpk1 (by rw [hVd]; omega)
    rw [hVd, hUd] at this
    exact this
  exact recheck_spec dn1 dn2 nu k vrest ulow (x.toNat * base + y.toNat) V W hV hW hnorm hvrest
    hulow hu2bound hWV _ _ hinv0 hrlt (by rw [hq0]; exact hle0)


/-! ## The main loop -/

public theorem base_pow (k : Nat) : base ^ k = 2 ^ (32 * k) := by rw [Nat.pow_mul]

public theorem Mag.valFrom_lt (a : Mag) (q i : Nat) : a.valFrom q i < 2 ^ (32 * i) := by
  induction i with
  | zero => simp [Mag.valFrom]
  | succ i ih =>
    rw [Mag.valFrom, show 32 * (i + 1) = 32 * i + 32 by omega, Nat.pow_add]
    have hd := a.digit_lt (q + i)
    have h1 : a.digit (q + i) * 2 ^ (32 * i) ≤ (2 ^ 32 - 1) * 2 ^ (32 * i) :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : (2 ^ 32 - 1) * 2 ^ (32 * i) + 2 ^ (32 * i) = 2 ^ (32 * i) * 2 ^ 32 := by
      rw [Nat.sub_mul, Nat.one_mul, Nat.mul_comm (2 ^ (32 * i))]
      have : 2 ^ (32 * i) ≤ 2 ^ 32 * 2 ^ (32 * i) := Nat.le_mul_of_pos_left _ (by simp)
      omega
    omega

public theorem Mag.valUpTo_succ_div (a : Mag) (m : Nat) : a.valUpTo (m + 1) / 2 ^ (32 * m) = a.digit m := by
  rw [Mag.valUpTo, Nat.add_comm, Nat.mul_comm (a.digit m), Nat.mul_add_div (Nat.two_pow_pos _),
    Nat.div_eq_of_lt (a.valUpTo_lt m), Nat.add_zero]

/--
After subtracting `qh * V` from the window `W` (with `W / V ≤ qh ≤ W / V + 1`), either nothing
borrowed and `qh` is exact, or the subtraction borrowed, `qh` is one too big, and the top digit of
the window is nonzero. `P = 2^(32 j)` scales the window, `Bn = 2^(32 n)`.
-/
public theorem divN_arith (Lo P W V qh k Z1 Bn : Nat) (hP : 0 < P) (hLo : Lo < P) (hV : 0 < V)
    (hVB : V < Bn) (hq1 : W / V ≤ qh) (hq2 : qh ≤ W / V + 1) (hk : k < 2)
    (h6 : Z1 + qh * V * P = Lo + P * W + k * (P * Bn * 2 ^ 32)) (hZ1 : Z1 < P * Bn * 2 ^ 32) :
    (k = 0 ∧ qh = W / V ∧ Z1 = Lo + P * (W % V) ∧ Z1 < P * Bn) ∨
      (k = 1 ∧ qh = W / V + 1 ∧ Z1 + V * P = Lo + P * (W % V) + P * Bn * 2 ^ 32 ∧ P * Bn ≤ Z1) := by
  have hW := Nat.div_add_mod W V
  have hr := Nat.mod_lt W hV
  have hPr : P * (W % V) + P ≤ P * V := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hr
  have hPV : P * V + P ≤ P * Bn := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hVB
  have hBig : P * Bn * 2 ^ 32 = P * Bn + P * Bn * (2 ^ 32 - 1) := by
    rw [Nat.mul_sub, Nat.mul_one]
    have : P * Bn ≤ P * Bn * 2 ^ 32 := Nat.le_mul_of_pos_right _ (by simp)
    omega
  have hBig2 : P * Bn ≤ P * Bn * (2 ^ 32 - 1) := Nat.le_mul_of_pos_right _ (by simp)
  have e1 : P * W = W / V * V * P + P * (W % V) := by
    conv => lhs; rw [← hW]
    rw [Nat.mul_add, Nat.mul_comm V, Nat.mul_comm P (W / V * V)]
  have hVP : V * P = P * V := Nat.mul_comm _ _
  rw [e1] at h6
  rcases (show qh = W / V ∨ qh = W / V + 1 by omega) with hq | hq <;> subst hq
  · left
    have hk0 : k = 0 := by
      rcases (show k = 0 ∨ k = 1 by omega) with h | h
      · exact h
      · subst h; omega
    subst hk0
    refine ⟨rfl, rfl, by omega, by omega⟩
  · have e2 : (W / V + 1) * V * P = W / V * V * P + V * P := by
      rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]
    rw [e2] at h6
    right
    have hk1 : k = 1 := by
      rcases (show k = 0 ∨ k = 1 by omega) with h | h
      · subst h; omega
      · exact h
    subst hk1
    refine ⟨rfl, rfl, by omega, by omega⟩

public theorem divNLoop_spec (v : Mag) (n : USize) (hn2 hnv) (vtop vsec : UInt64) (j1 : USize)
    (q u ms : Mag) (hq hu hms) (dn1 dn2 : UInt32) (V U₀ : Nat)
    (hV : V = v.valUpTo n.toNat) (hvz : v.digit n.toNat = 0)
    (hd1 : dn1.toNat = v.digit (n.toNat - 1)) (hd2 : dn2.toNat = v.digit (n.toNat - 2))
    (hvtop : vtop = dn1.toUInt64) (hvsec : vsec = dn2.toUInt64) (hnorm : base ≤ 2 * dn1.toNat)
    (hinv : U₀ = q.val * V + u.val) (hlt : u.val < V * 2 ^ (32 * j1.toNat))
    (huz : ∀ p, j1.toNat + n.toNat ≤ p → u.digit p = 0)
    (hqz : ∀ p, p < j1.toNat → q.digit p = 0) :
    U₀ = (divNLoop v n hn2 hnv vtop vsec j1 q u ms hq hu hms).1.val * V +
        (divNLoop v n hn2 hnv vtop vsec j1 q u ms hq hu hms).2.val ∧
      (divNLoop v n hn2 hnv vtop vsec j1 q u ms hq hu hms).2.val < V ∧
      (∀ p, n.toNat ≤ p → (divNLoop v n hn2 hnv vtop vsec j1 q u ms hq hu hms).2.digit p = 0) := by
  subst hvtop hvsec
  have hVlt : V < 2 ^ (32 * n.toNat) := by rw [hV]; exact v.valUpTo_lt _
  have hdn1 : dn1.toNat < base := dn1.toNat_lt_size
  have hVdec : V = (dn1.toNat * base + dn2.toNat) * base ^ (n.toNat - 2) +
      v.valUpTo (n.toNat - 2) := by
    have e1 : v.valUpTo n.toNat = v.valUpTo (n.toNat - 2) +
        v.digit (n.toNat - 2) * 2 ^ (32 * (n.toNat - 2)) +
        v.digit (n.toNat - 1) * 2 ^ (32 * (n.toNat - 2) + 32) := by
      obtain ⟨m, hm⟩ : ∃ m, n.toNat = m + 2 := ⟨n.toNat - 2, by omega⟩
      rw [hm, show m + 2 - 2 = m by omega, show m + 2 - 1 = m + 1 by omega,
        show m + 2 = m + 1 + 1 by omega, Mag.valUpTo, Mag.valUpTo,
        show 32 * (m + 1) = 32 * m + 32 by omega]
    rw [hV, e1, ← hd1, ← hd2, base_pow, Nat.pow_add]
    generalize (2 : Nat) ^ (32 * (n.toNat - 2)) = X
    simp only [base_eq]
    grind
  have hVpos : 0 < V := by
    have h1 : 0 < dn1.toNat * base + dn2.toNat :=
      Nat.lt_of_lt_of_le (Nat.mul_pos (show 0 < dn1.toNat by simp only [base_eq] at hnorm; omega)
        (show 0 < base by decide)) (Nat.le_add_right _ _)
    have := Nat.mul_pos h1 (Nat.pow_pos (n := n.toNat - 2) (show 0 < base by decide))
    rw [hVdec]
    exact Nat.lt_of_lt_of_le this (Nat.le_add_right _ _)
  fun_induction divNLoop v n hn2 hnv dn1.toUInt64 dn2.toUInt64 j1 q u ms hq hu hms
  · rename_i q u ms hms hq hu
    simp only [USize.toNat_zero, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.zero_add] at hlt huz
    exact ⟨hinv, hlt, huz⟩
  all_goals
    rename_i j1 q u ms hq hu hms _ hj1 j hj hjn hjn1 hjn2 temp qh ms1 hms1 hn1 u1 hu1 hcond ih
    have hjv : j.toNat + 1 = j1.toNat := by omega
    have hx : (u.get (j + n) (by rw [hjn]; omega)).toNat = u.digit (j.toNat + n.toNat) := by
      rw [Mag.get_toNat, hjn]
    have hy : (u.get (j + n - 1) (by rw [hjn1]; omega)).toNat =
        u.digit (j.toNat + n.toNat - 1) := by rw [Mag.get_toNat, hjn1]
    have hnu : (u.get (j + n - 2) (by rw [hjn2]; omega)).toNat =
        u.digit (j.toNat + n.toNat - 2) := by rw [Mag.get_toNat, hjn2]
    -- the window `W` of `n + 1` digits at `j`
    have hZ : u.val = u.valUpTo (j.toNat + n.toNat + 1) := by
      rw [Mag.val, Mag.valUpTo_eq_of_zero u (j.toNat + n.toNat + 1) u.n (by omega)
        (fun p hp _ => huz p (by omega))]
    have hsplit := u.valUpTo_add j.toNat (n.toNat + 1)
    rw [show j.toNat + (n.toNat + 1) = j.toNat + n.toNat + 1 by omega] at hsplit
    have hWdec : u.valFrom j.toNat (n.toNat + 1) =
        ((u.get (j + n) (by rw [hjn]; omega)).toNat * base +
          (u.get (j + n - 1) (by rw [hjn1]; omega)).toNat) * base ^ (n.toNat - 2 + 1) +
        (u.get (j + n - 2) (by rw [hjn2]; omega)).toNat * base ^ (n.toNat - 2) +
        u.valFrom j.toNat (n.toNat - 2) := by
      rw [hx, hy, hnu, show n.toNat + 1 = (n.toNat - 2) + 1 + 1 + 1 by omega, Mag.valFrom,
        Mag.valFrom, Mag.valFrom, show j.toNat + (n.toNat - 2 + 1 + 1) = j.toNat + n.toNat by omega,
        show j.toNat + (n.toNat - 2 + 1) = j.toNat + n.toNat - 1 by omega,
        show j.toNat + (n.toNat - 2) = j.toNat + n.toNat - 2 by omega, base_pow, base_pow,
        show 32 * (n.toNat - 2 + 1 + 1) = 32 * (n.toNat - 2) + 32 + 32 by omega,
        show 32 * (n.toNat - 2 + 1) = 32 * (n.toNat - 2) + 32 by omega]
      simp only [Nat.pow_add, show (2 : Nat) ^ 32 = 4294967296 from rfl]
      generalize (2 : Nat) ^ (32 * (n.toNat - 2)) = X
      simp only [base_eq]
      grind
    have hulow := u.valFrom_lt j.toNat (n.toNat - 2)
    have hvrest := v.valUpTo_lt (n.toNat - 2)
    rw [← base_pow] at hulow hvrest
    have hP : 2 ^ (32 * j1.toNat) = 2 ^ (32 * j.toNat) * base := by
      rw [← hjv, show 32 * (j.toNat + 1) = 32 * j.toNat + 32 by omega, Nat.pow_add]
    have hWV : u.valFrom j.toNat (n.toNat + 1) < V * base := by
      rw [hZ, hsplit, hP] at hlt
      have : 2 ^ (32 * j.toNat) * u.valFrom j.toNat (n.toNat + 1) <
          2 ^ (32 * j.toNat) * (V * base) := by
        rw [show 2 ^ (32 * j.toNat) * (V * base) = V * (2 ^ (32 * j.toNat) * base) from
          Nat.mul_left_comm _ _ _]
        omega
      exact Nat.lt_of_mul_lt_mul_left this
    have hqh : qh.toNat < base ∧ u.valFrom j.toNat (n.toNat + 1) / V ≤ qh.toNat ∧
        qh.toNat ≤ u.valFrom j.toNat (n.toNat + 1) / V + 1 :=
      trial_spec dn1 dn2 _ _ _ (n.toNat - 2) (v.valUpTo (n.toNat - 2))
        (u.valFrom j.toNat (n.toNat - 2)) V _ hVdec hvrest hWdec hulow hnorm hWV
    -- multiply and subtract
    have hms1v : ms1.valUpTo (n.toNat + 1) = qh.toNat * V := by
      rw [hV]
      exact mul1Loop_spec qh (by simpa using hqh.1) v n hnv 0 0 ms hms (by simp) (by simp)
        (by simp [Mag.valUpTo])
    have hsub : ∃ k' : Nat, k' < 2 ∧
        u1.valUpTo (j.toNat + (n + 1).toNat) + ms1.valUpTo (n + 1).toNat * 2 ^ (32 * j.toNat) =
          u.valUpTo (j.toNat + (n + 1).toNat) + k' * 2 ^ (32 * (j.toNat + (n + 1).toNat)) :=
      subInPlace_spec ms1 (n + 1) j _ 0 0 u _ _ (by simp) _ (by simp [Mag.valUpTo])
    obtain ⟨k, hk, hsub⟩ := hsub
    rw [hn1, show j.toNat + (n.toNat + 1) = j.toNat + n.toNat + 1 by omega, hms1v] at hsub
    have hu1z : ∀ p, j.toNat + n.toNat + 1 ≤ p → u1.digit p = 0 := fun p hp => by
      rw [show u1.digit p = u.digit p from
        subInPlace_frame ms1 (n + 1) j _ 0 0 u _ _ p (Or.inr (by rw [hn1]; omega))]
      exact huz p (by omega)
    have htop1 : u1.digit (j.toNat + n.toNat) =
        u1.valUpTo (j.toNat + n.toNat + 1) / (2 ^ (32 * j.toNat) * 2 ^ (32 * n.toNat)) := by
      rw [← Nat.pow_add, ← Nat.mul_add, Mag.valUpTo_succ_div]
    have hget1 : (u1.get (j + n) (by rw [hjn]; omega)).toNat = u1.digit (j.toNat + n.toNat) := by
      rw [Mag.get_toNat, hjn]
    have hZ1lt := u1.valUpTo_lt (j.toNat + n.toNat + 1)
    rw [show 32 * (j.toNat + n.toNat + 1) = 32 * j.toNat + 32 * n.toNat + 32 by omega, Nat.pow_add,
      Nat.pow_add] at hZ1lt hsub
    have hLo := u.valUpTo_lt j.toNat
    have harith := divN_arith (u.valUpTo j.toNat) (2 ^ (32 * j.toNat))
      (u.valFrom j.toNat (n.toNat + 1)) V qh.toNat k (u1.valUpTo (j.toNat + n.toNat + 1))
      (2 ^ (32 * n.toNat)) (Nat.two_pow_pos _) hLo hVpos hVlt hqh.2.1 hqh.2.2 hk
      (by rw [← hsplit]; exact hsub) hZ1lt
    have hqv : q.digit j.toNat = 0 := hqz _ (by omega)
    have hdm := Nat.div_add_mod (u.valFrom j.toNat (n.toNat + 1)) V
    have hmodlt := Nat.mod_lt (u.valFrom j.toNat (n.toNat + 1)) hVpos
    have hPr : 2 ^ (32 * j.toNat) * (u.valFrom j.toNat (n.toNat + 1) % V) + 2 ^ (32 * j.toNat) ≤
        2 ^ (32 * j.toNat) * V := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hmodlt
    have hPV : 2 ^ (32 * j.toNat) * V ≤ 2 ^ (32 * j.toNat) * 2 ^ (32 * n.toNat) :=
      Nat.mul_le_mul_left _ (Nat.le_of_lt hVlt)
    -- the new state, given its window value
    have hnext : ∀ (u' : Mag) (d : UInt32) (hd : d.toNat = u.valFrom j.toNat (n.toNat + 1) / V)
        (hu'n : j.toNat + n.toNat + 1 ≤ u'.n)
        (hz' : ∀ p, j.toNat + n.toNat + 1 ≤ p → u'.digit p = 0)
        (hZ' : u'.valUpTo (j.toNat + n.toNat + 1) =
          u.valUpTo j.toNat + 2 ^ (32 * j.toNat) * (u.valFrom j.toNat (n.toNat + 1) % V)),
        U₀ = (q.set j (by omega) d).val * V + u'.val ∧ u'.val < V * 2 ^ (32 * j.toNat) ∧
          (∀ p, j.toNat + n.toNat ≤ p → u'.digit p = 0) ∧
          (∀ p, p < j.toNat → (q.set j (by omega) d).digit p = 0) := by
      intro u' d hd hu'n hz' hZ'
      have hval : u'.val = u'.valUpTo (j.toNat + n.toNat + 1) := by
        rw [Mag.val, Mag.valUpTo_eq_of_zero u' (j.toNat + n.toNat + 1) u'.n hu'n
          (fun p hp _ => hz' p hp)]
      rw [hval, hZ', Mag.val_set_of_zero q j _ d hqv, hd]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hinv, hZ, hsplit]
        generalize u.valFrom j.toNat (n.toNat + 1) / V = Wq at *
        generalize u.valFrom j.toNat (n.toNat + 1) % V = Wr at *
        generalize u.valFrom j.toNat (n.toNat + 1) = W at *
        subst hdm
        grind
      · rw [Nat.mul_comm V]; omega
      · intro p hp
        rcases Nat.lt_or_ge p (j.toNat + n.toNat + 1) with h | h
        · have hpe : p = j.toNat + n.toNat := by omega
          subst hpe
          have := u'.valUpTo_succ_div (j.toNat + n.toNat)
          rw [hZ', show 32 * (j.toNat + n.toNat) = 32 * j.toNat + 32 * n.toNat by omega,
            Nat.pow_add, Nat.div_eq_of_lt (by omega)] at this
          exact this.symm
        · exact hz' p h
      · intro p hp
        rw [Mag.digit_set, ite_eq_right (by omega), hqz p (by omega)]
  · -- the subtraction borrowed: add back once
    have hne : u1.digit (j.toNat + n.toNat) ≠ 0 := by
      have hc : u1.get (j + n) (by rw [hjn]; omega) ≠ 0 := by simpa using hcond
      rw [← hget1]; intro h0; exact hc (UInt32.toNat_inj.mp (by rw [h0]; rfl))
    rcases harith with ⟨-, -, -, hlt0⟩ | ⟨hk1, hqv', hZ1, hge⟩
    · exact absurd (by rw [htop1]; exact Nat.div_eq_of_lt hlt0) hne
    · have hadd : ∃ k' : Nat, k' < 2 ∧
          (addInPlace v (n + 1) j 0 0 u1 (by rw [hn1]; omega) (by simp)).valUpTo
              (j.toNat + n.toNat + 1) + k' * 2 ^ (32 * (j.toNat + n.toNat + 1)) =
            u1.valUpTo (j.toNat + n.toNat + 1) + v.valUpTo (n.toNat + 1) * 2 ^ (32 * j.toNat) :=
        addInPlace_spec v (n + 1) j 0 0 u1 _ _ (by simp) _ _ _ (by rw [hn1]) (by rw [hn1]; omega)
          (by simp [Mag.valUpTo])
      obtain ⟨k', hk', hadd⟩ := hadd
      have hv1 : v.valUpTo (n.toNat + 1) = V := by rw [Mag.valUpTo, hvz, Nat.zero_mul, Nat.add_zero, hV]
      rw [hv1,
        show 32 * (j.toNat + n.toNat + 1) = 32 * j.toNat + 32 * n.toNat + 32 by omega, Nat.pow_add,
        Nat.pow_add] at hadd
      have hZ2lt := (addInPlace v (n + 1) j 0 0 u1 (by rw [hn1]; omega) (by simp)).valUpTo_lt
        (j.toNat + n.toNat + 1)
      rw [show 32 * (j.toNat + n.toNat + 1) = 32 * j.toNat + 32 * n.toNat + 32 by omega, Nat.pow_add,
        Nat.pow_add] at hZ2lt
      have hk'1 : k' = 1 := by
        rcases (show k' = 0 ∨ k' = 1 by omega) with h | h
        · subst h; omega
        · exact h
      subst hk'1
      have hqpos : 0 < qh.toNat := by rw [hqv']; exact Nat.succ_pos _
      have hd : (qh.toUInt32 - 1).toNat = u.valFrom j.toNat (n.toNat + 1) / V := by
        have h1 : qh.toUInt32.toNat = qh.toNat := by
          rw [UInt64.toNat_toUInt32]; exact Nat.mod_eq_of_lt (by simpa using hqh.1)
        have h1' : (1 : UInt32).toNat ≤ qh.toUInt32.toNat := by
          rw [h1, UInt32.toNat_one]; exact hqpos
        rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr h1'), h1, UInt32.toNat_one, hqv',
          Nat.add_sub_cancel]
      have hu2n : j.toNat + n.toNat + 1 ≤ (addInPlace v (n + 1) j 0 0 u1 (by rw [hn1]; omega)
          (by simp)).n := by simp; omega
      obtain ⟨e1, e2, e3, e4⟩ := hnext _ _ hd hu2n (fun p hp => by
          rw [addInPlace_frame v (n + 1) j 0 0 u1 _ _ p (Or.inr (by rw [hn1]; omega))]
          exact hu1z p hp)
        (by omega)
      exact ih e1 e2 e3 e4
  · -- no borrow: the trial digit was exact
    have he : u1.digit (j.toNat + n.toNat) = 0 := by
      have hc : u1.get (j + n) (by rw [hjn]; omega) = 0 := by simpa using hcond
      rw [← hget1, hc]; rfl
    rcases harith with ⟨hk0, hqv', hZ1, hlt0⟩ | ⟨-, -, -, hge⟩
    · have hd : qh.toUInt32.toNat = u.valFrom j.toNat (n.toNat + 1) / V := by
        rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt (by simpa using hqh.1), hqv']
      obtain ⟨e1, e2, e3, e4⟩ := hnext u1 _ hd (by omega) hu1z hZ1
      exact ih e1 e2 e3 e4
    · rw [htop1] at he
      have := (Nat.div_eq_zero_iff_lt (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _))).mp he
      omega


/-! ## Normalization and the top level -/

public theorem UInt32.toNat_log2' (a : UInt32) : a.log2.toNat = Nat.log2 a.toNat := by
  unfold UInt32.log2 Fin.log2; rfl

public theorem Mag.digit_eq_zero_of_val_lt (v : Mag) (p : Nat) (h : v.val < 2 ^ (32 * p)) :
    v.digit p = 0 := by
  rw [← v.val_div_mod p, Nat.div_eq_of_lt h]

public theorem Mag.valUpTo_of_zero (a : Mag) (h : ∀ p, a.digit p = 0) (k : Nat) : a.valUpTo k = 0 := by
  rw [Mag.valUpTo_eq_of_zero a 0 k (Nat.zero_le _) (fun p _ _ => h p)]; rfl

public theorem Mag.val_of_zero (a : Mag) (h : ∀ p, a.digit p = 0) : a.val = 0 := a.valUpTo_of_zero h _

/-- Shifting the divisor by `31 - log2 top` sets the high bit of its top digit without growing it. -/
public theorem knuth_norm (b v : Mag) (hb : b.IsNorm) (hb2 : 2 ≤ b.n)
    (hv : v.val = b.val * 2 ^ (31 - Nat.log2 (b.digit (b.n - 1)))) (hvn : b.n ≤ v.n) :
    v.valUpTo b.n = v.val ∧ v.digit b.n = 0 ∧ 2 ^ 31 ≤ v.digit (b.n - 1) ∧
      v.val < 2 ^ (32 * b.n) := by
  have htop : b.digit (b.n - 1) ≠ 0 := by
    rcases hb with h | h
    · omega
    · exact h
  have htl := b.digit_lt (b.n - 1)
  have hbv : b.val = b.valUpTo (b.n - 1) + b.digit (b.n - 1) * 2 ^ (32 * (b.n - 1)) := by
    have h : b.valUpTo (b.n - 1 + 1) =
        b.valUpTo (b.n - 1) + b.digit (b.n - 1) * 2 ^ (32 * (b.n - 1)) := by rw [Mag.valUpTo]
    rw [show b.n - 1 + 1 = b.n by omega] at h
    exact h
  have hlo := b.valUpTo_lt (b.n - 1)
  generalize b.digit (b.n - 1) = top at htop htl hv hbv
  generalize b.valUpTo (b.n - 1) = lo at hbv hlo
  have hL1 := Nat.log2_self_le htop
  have hL2 := Nat.lt_log2_self (n := top)
  have hL3 : Nat.log2 top < 32 := (Nat.log2_lt htop).mpr htl
  generalize hL : Nat.log2 top = L at hL1 hL2 hL3 hv
  generalize hX : 2 ^ (32 * (b.n - 1)) = X at hbv hlo
  have hXpos : 0 < X := by rw [← hX]; exact Nat.two_pow_pos _
  have hEpos : 0 < 2 ^ (31 - L) := Nat.two_pow_pos _
  have hBn : 2 ^ (32 * b.n) = X * 2 ^ 32 := by
    rw [← hX, ← Nat.pow_add, show 32 * (b.n - 1) + 32 = 32 * b.n by omega]
  have h4 : 2 ^ (L + 1) * X * 2 ^ (31 - L) = X * 2 ^ 32 := by
    rw [Nat.mul_comm (2 ^ (L + 1)) X, Nat.mul_assoc, ← Nat.pow_add, show L + 1 + (31 - L) = 32 by omega]
  have h6 : 2 ^ L * X * 2 ^ (31 - L) = X * 2 ^ 31 := by
    rw [Nat.mul_comm (2 ^ L) X, Nat.mul_assoc, ← Nat.pow_add, show L + (31 - L) = 31 by omega]
  have hup : v.val < X * 2 ^ 32 := by
    have h1 : lo + top * X < (top + 1) * X := by rw [Nat.add_mul, Nat.one_mul]; omega
    have h2 : (top + 1) * X ≤ 2 ^ (L + 1) * X := Nat.mul_le_mul_right _ hL2
    rw [hv, hbv, ← h4]
    exact Nat.mul_lt_mul_of_pos_right (Nat.lt_of_lt_of_le h1 h2) hEpos
  have hdown : X * 2 ^ 31 ≤ v.val := by
    rw [hv, hbv, ← h6]
    exact Nat.mul_le_mul_right _ (Nat.le_trans (Nat.mul_le_mul_right X hL1) (Nat.le_add_left _ _))
  have hlt : v.val < 2 ^ (32 * b.n) := by rw [hBn]; exact hup
  have hzero : ∀ p, b.n ≤ p → v.digit p = 0 := fun p hp =>
    v.digit_eq_zero_of_val_lt p (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) (by omega)))
  refine ⟨?_, hzero _ (Nat.le_refl _), ?_, hlt⟩
  · rw [Mag.val, Mag.valUpTo_eq_of_zero v b.n v.n hvn (fun p hp _ => hzero p hp)]
  · rw [← v.val_div_mod (b.n - 1), hX]
    have hq1 : 2 ^ 31 ≤ v.val / X := (Nat.le_div_iff_mul_le hXpos).mpr (by rw [Nat.mul_comm]; exact hdown)
    have hq2 : v.val / X < 2 ^ 32 := (Nat.div_lt_iff_lt_mul hXpos).mpr (by rw [Nat.mul_comm]; exact hup)
    rw [Nat.mod_eq_of_lt hq2]
    exact hq1

public theorem knuth_core (a b v u q0 ms : Mag) (_ha : a.IsNorm) (hb : b.IsNorm) (hb2 : 2 ≤ b.n)
    (hba : b.n ≤ a.n) (s : Nat) (hs : s = 31 - Nat.log2 (b.digit (b.n - 1)))
    (hv : v.val = b.val * 2 ^ s) (hu : u.val = a.val * 2 ^ s) (hun : u.n = a.n + 1)
    (hq0 : ∀ p, q0.digit p = 0) (lb j1 : USize) (hlb : lb.toNat = b.n)
    (hj1 : j1.toNat = a.n - b.n + 1) (hn2 hnv hq hu' hms) (hg1 hg2) :
    (divNLoop v lb hn2 hnv (v.get (lb - 1) hg1).toUInt64 (v.get (lb - 2) hg2).toUInt64 j1 q0 u ms hq
        hu' hms).1.val = a.val / b.val ∧
      (divNLoop v lb hn2 hnv (v.get (lb - 1) hg1).toUInt64 (v.get (lb - 2) hg2).toUInt64 j1 q0 u ms
        hq hu' hms).2.val = a.val % b.val * 2 ^ s ∧
      (∀ p, b.n ≤ p → (divNLoop v lb hn2 hnv (v.get (lb - 1) hg1).toUInt64
        (v.get (lb - 2) hg2).toUInt64 j1 q0 u ms hq hu' hms).2.digit p = 0) := by
  obtain ⟨hvV, hvz, hvtop, hvlt⟩ := knuth_norm b v hb hb2 (hs ▸ hv) (by rw [← hlb]; exact hnv)
  have hlb1 : (lb - 1).toNat = b.n - 1 := by rw [toNat_pred (by omega), hlb]
  have hlb2 : (lb - 2).toNat = b.n - 2 := by rw [toNat_sub_two (by omega), hlb]
  have hbpos : 0 < b.val := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) (b.pow_le_val hb (by omega))
  have hEpos : 0 < 2 ^ s := Nat.two_pow_pos _
  have hd1 : (v.get (lb - 1) hg1).toNat = v.digit (lb.toNat - 1) := by
    rw [Mag.get_toNat, hlb1, hlb]
  have hd2 : (v.get (lb - 2) hg2).toNat = v.digit (lb.toNat - 2) := by
    rw [Mag.get_toNat, hlb2, hlb]
  have hspec := divNLoop_spec v lb hn2 hnv _ _ j1 q0 u ms hq hu' hms (v.get (lb - 1) hg1)
    (v.get (lb - 2) hg2) v.val u.val (by rw [hlb, hvV]) (by rw [hlb]; exact hvz) hd1 hd2 rfl rfl
    (by rw [hd1, hlb]; simp only [base_eq]; omega)
    (by rw [q0.val_of_zero hq0]; simp)
    (by
      rw [hu, hv, hj1]
      -- `a < b * B^(a.n - b.n + 1)` since `a < B^a.n` and `B^(b.n - 1) ≤ b`
      have h1 := a.val_lt
      have h2 := b.pow_le_val hb (by omega)
      have h3 : 2 ^ (32 * a.n) ≤ b.val * 2 ^ (32 * (a.n - b.n + 1)) := by
        rw [show 32 * a.n = 32 * (b.n - 1) + 32 * (a.n - b.n + 1) by omega, Nat.pow_add]
        exact Nat.mul_le_mul_right _ h2
      rw [Nat.mul_right_comm]
      exact Nat.mul_lt_mul_of_pos_right (Nat.lt_of_lt_of_le h1 h3) hEpos)
    (fun p hp => u.digit_of_n_le p (by omega))
    (fun p _ => hq0 p)
  obtain ⟨h1, h2, h3⟩ := hspec
  generalize (divNLoop v lb hn2 hnv (v.get (lb - 1) hg1).toUInt64 (v.get (lb - 2) hg2).toUInt64 j1 q0
    u ms hq hu' hms) = r at h1 h2 h3 ⊢
  rw [hu, hv] at h1
  rw [hv] at h2
  have hdiv : a.val * 2 ^ s / (b.val * 2 ^ s) = r.1.val := by
    rw [h1, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.mul_pos hbpos hEpos), Nat.div_eq_of_lt h2,
      Nat.zero_add]
  have hmod : a.val * 2 ^ s % (b.val * 2 ^ s) = r.2.val := by
    rw [h1, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h2]
  rw [Nat.mul_div_mul_right _ _ hEpos] at hdiv
  rw [Nat.mul_mod_mul_right] at hmod
  exact ⟨hdiv.symm, hmod.symm, fun p hp => h3 p (by rw [hlb]; exact hp)⟩

public theorem toNat_shift31 (x : UInt32) : (31 - x.log2).toNat = 31 - Nat.log2 x.toNat := by
  have h : Nat.log2 x.toNat ≤ 31 := by
    rcases Nat.eq_zero_or_pos x.toNat with h0 | h0
    · rw [h0]; simp [Nat.log2_zero]
    · have := (Nat.log2_lt (by omega)).mpr x.toNat_lt; omega
  rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by rw [UInt32.toNat_log2']; simpa using h)),
    UInt32.toNat_log2']
  simp

public theorem val_shiftDivisor (b : Mag) (s : UInt32) (h) (hs : s.toNat < 32) :
    (shiftDivisor b b.usize b.usize_toNat s h).1.val = b.val * 2 ^ s.toNat := by
  unfold shiftDivisor
  split
  · next h0 =>
    have : s.toNat = 0 := by simpa [← UInt32.toNat_inj] using h0
    simp [this]
  · next h0 =>
    have hs0 : 0 < s.toNat := by
      have : s.toNat ≠ 0 := fun h' => h0 (by simpa [← UInt32.toNat_inj] using h')
      omega
    dsimp only
    rw [shlLoop_val _ _ _ hs0 hs _ _ _ (fun p => Mag.digit_zeros _ _ _)
      (by rw [Mag.n_zeros, b.usize_succ_toNat]; simp)]
    simp

public theorem val_shiftDividend (a : Mag) (s : UInt32) (h) (hs : s.toNat < 32) :
    (shiftDividend a a.usize a.usize_toNat s h).1.val = a.val * 2 ^ s.toNat := by
  unfold shiftDividend
  split
  · next h0 =>
    have : s.toNat = 0 := by simpa [← UInt32.toNat_inj] using h0
    dsimp only
    rw [copyLoop_val _ _ _ _ _ (fun p => Mag.digit_zeros _ _ _)
      (by rw [Mag.n_zeros, a.usize_succ_toNat]; simp)]
    simp [this]
  · next h0 =>
    have hs0 : 0 < s.toNat := by
      have : s.toNat ≠ 0 := fun h' => h0 (by simpa [← UInt32.toNat_inj] using h')
      omega
    dsimp only
    rw [shlLoop_val _ _ _ hs0 hs _ _ _ (fun p => Mag.digit_zeros _ _ _)
      (by rw [Mag.n_zeros, a.usize_succ_toNat]; simp)]
    simp

public theorem val_knuthRem (u : Mag) (lb : USize) (hlb) (s : UInt32) (h) (hs : s.toNat < 32)
    (hz : ∀ p, lb.toNat ≤ p → u.digit p = 0) :
    (knuthRem u lb hlb s h).val = u.val / 2 ^ s.toNat := by
  have ht : (u.take lb hlb).val = u.val := by
    rw [Mag.val_take, Mag.val, Mag.valUpTo_eq_of_zero u lb.toNat u.n hlb (fun p hp _ => hz p hp)]
  unfold knuthRem
  split
  · next h0 =>
    have : s.toNat = 0 := by simpa [← UInt32.toNat_inj] using h0
    rw [ht, this]; simp
  · next h0 =>
    have hs0 : 0 < s.toNat := by
      have : s.toNat ≠ 0 := fun h' => h0 (by simpa [← UInt32.toNat_inj] using h')
      omega
    rw [shrLoop_val' _ _ _ _ hs0 hs _ _ _ _ (by simp), ← ht]
    congr 1
    have := (u.take lb hlb).valUpTo_add 0 lb.toNat
    rw [Nat.zero_add, Nat.mul_zero, Nat.pow_zero, Nat.one_mul] at this
    rw [Mag.val, Mag.n_take, this]
    simp [Mag.valUpTo]

public theorem knuthCore_spec (a b : Mag) (h) (s : UInt32) (v u) (ha : a.IsNorm) (hb : b.IsNorm)
    (hs32 : s.toNat < 32) (hsS : s.toNat = 31 - Nat.log2 (b.digit (b.n - 1)))
    (hv : v.1.val = b.val * 2 ^ s.toNat) (hu : u.1.val = a.val * 2 ^ s.toNat) :
    (knuthCore a b h s v u).1.val = a.val / b.val ∧ (knuthCore a b h s v u).2.val = a.val % b.val ∧
      (knuthCore a b h s v u).1.IsNorm ∧ (knuthCore a b h s v u).2.IsNorm := by
  have hla := a.usize_toNat
  have hlb := b.usize_toNat
  have hb2 := h.1
  have hba := h.2.1
  have hfit := h.2.2
  have hlb1 : (b.usize - 1).toNat = b.n - 1 := by rw [toNat_pred (by omega), hlb]
  have hm : (a.usize - b.usize).toNat = a.n - b.n := by
    rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr (by omega)), hla, hlb]
  have hm1 : (a.usize - b.usize + 1).toNat = a.n - b.n + 1 := by
    rw [toNat_succ_of_lt_size (by have := maxBytes_lt; omega), hm]
  have hlb1' : (b.usize + 1).toNat = b.n + 1 := b.usize_succ_toNat
  have hk := knuth_core a b v.1 u.1 (Mag.zeros (a.usize - b.usize + 1) (by omega))
    (Mag.zeros (b.usize + 1) (by omega)) ha hb hb2 hba _ hsS hv hu
    (by rw [u.2, hla]) (fun p => Mag.digit_zeros _ _ _) b.usize (a.usize - b.usize + 1) hlb hm1
    (by omega) v.2 (by simp) (by rw [u.2]; omega) (by simp only [Mag.n_zeros]; omega)
    (by rw [hlb1]; have := v.2; omega) (by rw [toNat_sub_two (by omega)]; have := v.2; omega)
  unfold knuthCore
  dsimp only
  refine ⟨?_, ?_, Mag.isNorm_normalize _, Mag.isNorm_normalize _⟩
  · rw [Mag.val_normalize]; exact hk.1
  · rw [Mag.val_normalize, val_knuthRem _ _ _ _ _ hs32 (fun p hp => hk.2.2 p (by rw [← hlb]; exact hp)),
      hk.2.1, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

/-- Knuth's algorithm D computes quotient and remainder. -/
public theorem knuth_spec (a b : Mag) (h) (ha : a.IsNorm) (hb : b.IsNorm) :
    (knuth a b h).1.val = a.val / b.val ∧ (knuth a b h).2.val = a.val % b.val ∧
      (knuth a b h).1.IsNorm ∧ (knuth a b h).2.IsNorm := by
  have hlb := b.usize_toNat
  have hb2 := h.1
  have hfit := h.2.2
  have hlb1 : (b.usize - 1).toNat = b.n - 1 := by rw [toNat_pred (by omega), hlb]
  have hS32 : (31 - (b.get (b.usize - 1) (by omega)).log2).toNat < 32 := by
    rw [toNat_shift31]; omega
  have hsS : (31 - (b.get (b.usize - 1) (by omega)).log2).toNat =
      31 - Nat.log2 (b.digit (b.n - 1)) := by
    rw [toNat_shift31, Mag.get_toNat, hlb1]
  unfold knuth
  exact knuthCore_spec a b h _ _ _ ha hb hS32 hsS (val_shiftDivisor b _ _ hS32)
    (val_shiftDividend a _ _ hS32)

public theorem val_ofUInt64 (x : UInt64) : (ofUInt64 x).val = x.toNat ∧ (ofUInt64 x).IsNorm := by
  refine ⟨?_, Mag.isNorm_normalize _⟩
  unfold ofUInt64
  dsimp only
  rw [Mag.val_normalize, Mag.val]
  simp only [Mag.n_set, Mag.n_zeros, two_usize_toNat]
  simp only [Mag.valUpTo, Mag.digit_set, Mag.digit_zeros]
  simp only [USize.toNat_zero, USize.toNat_one, ite_eq_left]
  have h1 : x.toUInt32.toNat = x.toNat % 2 ^ 32 := by simp
  have h2 : (x >>> 32).toUInt32.toNat = x.toNat / 2 ^ 32 := by
    have hx := x.toNat_lt
    simp only [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    rw [show (32 : UInt64).toNat % 64 = 32 from rfl]
    exact Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (by simpa using hx))
  simp [h1, h2]
  have := Nat.mod_add_div x.toNat (2 ^ 32)
  omega

/-- Long division computes quotient and remainder (with `a / 0 = 0` and `a % 0 = a`). -/
public theorem divModBasecase_spec (a b : Mag) (ha : a.IsNorm) (hb : b.IsNorm)
    (hfit : (a.n + 1) * 4 ≤ maxBytes) :
    (divModBasecase a b).1.val = a.val / b.val ∧ (divModBasecase a b).2.val = a.val % b.val ∧
      (divModBasecase a b).1.IsNorm ∧ (divModBasecase a b).2.IsNorm := by
  have hcmp := cmp_spec a b ha hb
  unfold divModBasecase
  split
  · next hlt =>
    rw [hcmp] at hlt
    have hlt' : a.val < b.val := Nat.compare_eq_lt.mp (by simpa using hlt)
    exact ⟨by rw [Mag.val_empty, Nat.div_eq_of_lt hlt'], by rw [Nat.mod_eq_of_lt hlt'],
      Mag.isNorm_empty, ha⟩
  · next hnlt =>
    split
    · next h1 =>
      have hn1 : b.n = 1 := by have := b.usize_toNat; rw [h1] at this; simpa using this.symm
      have hbv : b.val = b.digit 0 := by rw [Mag.val, hn1]; simp [Mag.valUpTo]
      have hd : (b.get 0 (by rw [USize.toNat_zero]; omega)).toNat = b.digit 0 := by rw [Mag.get_toNat]; rfl
      have hd0 : 0 < (b.get 0 (by rw [USize.toNat_zero]; omega)).toNat := by
        rw [hd]
        rcases hb with h | h
        · omega
        · rw [hn1] at h; exact Nat.pos_of_ne_zero h
      obtain ⟨hq, hr, hqn⟩ := val_divModSmall a _ hd0
      dsimp only
      rw [hd] at hq hr
      obtain ⟨hv, hvn⟩ := val_ofUInt64 (divModSmall a (b.get 0 (by rw [USize.toNat_zero]; omega))).2.toUInt64
      refine ⟨by rw [hq, hbv], ?_, hqn, hvn⟩
      rw [hv, UInt32.toNat_toUInt64, hr, hbv]
    · next h1 =>
      split
      · next h2 =>
        exact knuth_spec a b _ ha hb
      · next h2 =>
        -- only `b = 0` remains: a nonzero `b` longer than `a` would compare greater
        have hb0 : b.n = 0 := by
          have hn1 : b.n ≠ 1 := fun h' => h1 (by
            apply USize.toNat_inj.mp; rw [b.usize_toNat, h']; simp)
          rcases Nat.lt_or_ge b.n 2 with h | h
          · omega
          · exfalso
            have hgt : a.n < b.n := by omega
            have h3 := a.val_lt
            have h4 := b.pow_le_val hb (by omega)
            have h5 : 2 ^ (32 * a.n) ≤ 2 ^ (32 * (b.n - 1)) := Nat.pow_le_pow_right (by omega) (by omega)
            have hlt : a.val < b.val := by omega
            apply hnlt
            rw [hcmp]
            simp [Nat.compare_eq_lt.mpr hlt]
        have hbv : b.val = 0 := by rw [Mag.val, hb0]; rfl
        exact ⟨by rw [hbv, Mag.val_empty, Nat.div_zero], by rw [hbv, Nat.mod_zero], Mag.isNorm_empty, ha⟩

end Nat.Big
