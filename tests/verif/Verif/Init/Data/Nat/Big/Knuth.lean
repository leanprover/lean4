module

import all Init.Data.ByteArray.Basic
import all Init.Data.ByteArray.Extra
import all Init.Data.UInt.Log2
import all Init.Data.Fin.Log2
public import Init.Data.Nat.Big

/-! Arithmetic facts behind Knuth's algorithm D, ported from the `mpn_model` proof. -/

namespace Nat.Big

public abbrev base : Nat := 4294967296
public theorem base_eq : base = 4294967296 := rfl

namespace KnuthD


/-- Knuth 4.3.1 Theorem A: the trial quotient digit is never too small. -/
public theorem le_qhat {u v P : Nat} (hP : 0 < P) (hv : 0 < v / P) :
    u / v ≤ (u / P) / (v / P) := by
  calc u / v ≤ u / (P * (v / P)) :=
        Nat.div_le_div_left (Nat.mul_div_le v P) (Nat.mul_pos hP hv)
    _ = u / P / (v / P) := (Nat.div_div_eq_div_mul u P (v / P)).symm

/--
Knuth 4.3.1 exercise 19: when step D3's test fires, the trial digit really is
too big, so decrementing it cannot undershoot the true quotient digit.
-/
public theorem lt_of_test {b k vtop vsnd vrest u u2 u3 ulow qhat rhat : Nat}
    (hu : u = u2 * b ^ (k+1) + u3 * b ^ k + ulow) (hulow : ulow < b ^ k)
    (hu2 : u2 = qhat * vtop + rhat)
    (hfire : b * rhat + u3 < qhat * vsnd) :
    u < qhat * ((vtop * b + vsnd) * b ^ k + vrest) := by
  have hpow : b ^ (k+1) = b ^ k * b := Nat.pow_succ b k
  calc u = u2 * (b ^ k * b) + u3 * b ^ k + ulow := by rw [hu, hpow]
    _ < qhat * vtop * (b ^ k * b) + (b * rhat + u3 + 1) * b ^ k := by
        rw [hu2]; have : (qhat * vtop + rhat) * (b ^ k * b) + u3 * b ^ k + b ^ k
            = qhat * vtop * (b ^ k * b) + (b * rhat + u3 + 1) * b ^ k := by grind
        omega
    _ ≤ qhat * vtop * (b ^ k * b) + (qhat * vsnd) * b ^ k :=
        Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
    _ = qhat * ((vtop * b + vsnd) * b ^ k) := by grind
    _ ≤ qhat * ((vtop * b + vsnd) * b ^ k + vrest) :=
        Nat.mul_le_mul_left _ (Nat.le_add_right _ _)

/--
The converse: when step D3's test fails, the trial digit is at most one too big,
which is exactly what makes the single add-back of step D6 enough. Only
`1 ≤ vtop` and `qhat < b` are needed, not the full normalization.
-/
public theorem le_succ_of_not_test {b k vtop vsnd vrest u u2 u3 ulow qhat rhat : Nat}
    (hu : u = u2 * b ^ (k+1) + u3 * b ^ k + ulow)
    (hu2 : u2 = qhat * vtop + rhat)
    (hvrest : vrest < b ^ k) (hvtop : 1 ≤ vtop) (hqhat : qhat < b)
    (hfail : qhat * vsnd ≤ b * rhat + u3) :
    qhat * ((vtop * b + vsnd) * b ^ k + vrest)
      ≤ u + ((vtop * b + vsnd) * b ^ k + vrest) := by
  -- `qhat` times the divisor's leading part already fits under `u`
  have hmain : qhat * ((vtop * b + vsnd) * b ^ k) ≤ u := by
    calc qhat * ((vtop * b + vsnd) * b ^ k)
        = qhat * vtop * (b ^ k * b) + (qhat * vsnd) * b ^ k := by grind
      _ ≤ qhat * vtop * (b ^ k * b) + (b * rhat + u3) * b ^ k :=
          Nat.add_le_add_left (Nat.mul_le_mul_right _ hfail) _
      _ = u2 * (b ^ k * b) + u3 * b ^ k := by grind
      _ ≤ u := by grind
  -- and the low part of the divisor that this ignores is itself below the divisor
  have hslack : qhat * vrest ≤ (vtop * b + vsnd) * b ^ k + vrest := by
    have h1 : qhat * vrest ≤ b * b ^ k := Nat.mul_le_mul (by omega) (by omega)
    have h2 : b * b ^ k ≤ (vtop * b + vsnd) * b ^ k := by
      refine Nat.mul_le_mul_right _ ?_
      calc b = 1 * b := (Nat.one_mul b).symm
        _ ≤ vtop * b := Nat.mul_le_mul_right b hvtop
        _ ≤ vtop * b + vsnd := Nat.le_add_right _ _
    exact Nat.le_trans (Nat.le_trans h1 h2) (Nat.le_add_right _ _)
  grind

/-!
Restated against the divisor `v` and the true quotient digit `u / v`, which is
the form the loop proof consumes: after step D3 the trial digit is either exact
or one too big, and every decrement it performs is justified.
-/

/-- A trial digit whose test fires is strictly above the true quotient digit. -/
public theorem div_lt_of_test {b k vtop vsnd vrest v u u2 u3 ulow qhat rhat : Nat}
    (hv : v = (vtop * b + vsnd) * b ^ k + vrest) (hvpos : 0 < v)
    (hu : u = u2 * b ^ (k+1) + u3 * b ^ k + ulow) (hulow : ulow < b ^ k)
    (hu2 : u2 = qhat * vtop + rhat)
    (hfire : b * rhat + u3 < qhat * vsnd) :
    u / v < qhat :=
  (Nat.div_lt_iff_lt_mul hvpos).mpr <| by
    have := lt_of_test (vrest := vrest) hu hulow hu2 hfire
    rw [hv]; omega

/-- A trial digit whose test fails is at most one above the true quotient digit. -/
public theorem le_succ_div_of_not_test {b k vtop vsnd vrest v u u2 u3 ulow qhat rhat : Nat}
    (hv : v = (vtop * b + vsnd) * b ^ k + vrest) (hvpos : 0 < v)
    (hu : u = u2 * b ^ (k+1) + u3 * b ^ k + ulow)
    (hu2 : u2 = qhat * vtop + rhat)
    (hvrest : vrest < b ^ k) (hvtop : 1 ≤ vtop) (hqhat : qhat < b)
    (hfail : qhat * vsnd ≤ b * rhat + u3) :
    qhat ≤ u / v + 1 := by
  have hle : qhat * v ≤ u + v := by
    have := le_succ_of_not_test (vsnd := vsnd) hu hu2 hvrest hvtop hqhat hfail
    rw [hv]; omega
  rcases qhat with _ | m
  · exact Nat.zero_le _
  · have hm : m * v ≤ u := by
      have : (m+1) * v = m * v + v := by grind
      omega
    have := (Nat.le_div_iff_mul_le hvpos).mpr hm
    omega

end KnuthD

public theorem q_le_of_inv {q r vtop u2 : Nat} (hinv : u2 = q * vtop + r)
    (hu2 : u2 ≤ vtop * base + (base - 1)) (hnorm : base ≤ 2 * vtop) : q ≤ base + 1 := by
  rcases Nat.lt_or_ge q (base + 2) with h | h
  · omega
  · exfalso
    have h1 : (base + 2) * vtop ≤ q * vtop := Nat.mul_le_mul_right _ h
    simp only [base_eq] at *
    omega

public theorem recheck_test_iff (dn2 nu : UInt32) (q r : UInt64)
    (hq : q.toNat ≤ base + 1) (hr : r.toNat < base) :
    ((q ≥ BASE || q * dn2.toUInt64 > (r <<< 32) + nu.toUInt64) = true)
      = (base ≤ q.toNat ∨ base * r.toNat + nu.toNat < q.toNat * dn2.toNat) := by
  have hd2 : dn2.toNat < base := dn2.toNat_lt_size
  have hnu : nu.toNat < base := nu.toNat_lt_size
  have hmul : (q * dn2.toUInt64).toNat = q.toNat * dn2.toNat := by
    rw [UInt64.toNat_mul, UInt32.toNat_toUInt64]
    refine Nat.mod_eq_of_lt ?_
    calc q.toNat * dn2.toNat ≤ (base + 1) * (base - 1) := Nat.mul_le_mul hq (by omega)
      _ < 2 ^ 64 := by simp only [base_eq]; omega
  have hshl : ((r <<< 32) + nu.toUInt64).toNat = base * r.toNat + nu.toNat := by
    have h1 : (r <<< 32).toNat = r.toNat * 4294967296 := by
      rw [UInt64.toNat_shiftLeft, show (32 : UInt64).toNat % 64 = 32 from rfl, Nat.shiftLeft_eq]
      simp only [base_eq] at hr
      exact Nat.mod_eq_of_lt (by omega)
    rw [UInt64.toNat_add, UInt32.toNat_toUInt64, h1]
    simp only [base_eq] at hr hnu ⊢
    omega
  have hB : BASE.toNat = base := rfl
  simp only [ge_iff_le, gt_iff_lt, UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt, hmul, hshl, hB,
    Bool.or_eq_true, decide_eq_true_eq]

public theorem toNat_pred64 {q : UInt64} (h : 0 < q.toNat) : (q - 1).toNat = q.toNat - 1 := by
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]
  simp

public theorem toNat_add_digit (r : UInt64) (d : UInt32) (hr : r.toNat < base) :
    (r + d.toUInt64).toNat = r.toNat + d.toNat := by
  have hd : d.toNat < base := d.toNat_lt_size
  simp only [base_eq] at hr hd
  rw [UInt64.toNat_add, UInt32.toNat_toUInt64]
  exact Nat.mod_eq_of_lt (by omega)

/--
Step D3's postcondition: the trial digit fits in a single digit and is either exact or one too
big, so the single add-back of step D6 suffices.
-/
public theorem recheck_spec (dn1 dn2 nu : UInt32) (k vrest ulow u2 V U : Nat)
    (hV : V = (dn1.toNat * base + dn2.toNat) * base ^ k + vrest)
    (hU : U = u2 * base ^ (k+1) + nu.toNat * base ^ k + ulow)
    (hnorm : base ≤ 2 * dn1.toNat)
    (hvrest : vrest < base ^ k) (hulow : ulow < base ^ k)
    (hu2 : u2 ≤ dn1.toNat * base + (base - 1))
    (hUV : U < V * base) (q r : UInt64)
    (hinv : u2 = q.toNat * dn1.toNat + r.toNat) (hr : r.toNat < base) (hle : U / V ≤ q.toNat) :
    (recheck q r dn1.toUInt64 dn2.toUInt64 nu.toUInt64).toNat < base ∧
      U / V ≤ (recheck q r dn1.toUInt64 dn2.toUInt64 nu.toUInt64).toNat ∧
      (recheck q r dn1.toUInt64 dn2.toUInt64 nu.toUInt64).toNat ≤ U / V + 1 := by
  have hvtop1 : 1 ≤ dn1.toNat := by simp only [base_eq] at hnorm; omega
  have hd2 : dn2.toNat < base := dn2.toNat_lt_size
  have hVpos : 0 < V := by
    have h1 : 1 * base ^ k ≤ (dn1.toNat * base + dn2.toNat) * base ^ k :=
      Nat.mul_le_mul_right _ (by simp only [base_eq] at hvtop1 ⊢; omega)
    have : 0 < base ^ k := Nat.pow_pos (by simp)
    omega
  have hqlt : U / V < base := Nat.div_lt_of_lt_mul hUV
  fun_induction recheck q r dn1.toUInt64 dn2.toUInt64 nu.toUInt64 with
  | case1 q r hfire q' r' hr' ih =>
    have hq := q_le_of_inv hinv hu2 hnorm
    have hdec : U / V < q.toNat := by
      rw [recheck_test_iff dn2 nu q r hq hr] at hfire
      rcases hfire with h | h
      · omega
      · exact KnuthD.div_lt_of_test hV hVpos hU hulow hinv h
    have hqpos : 0 < q.toNat := Nat.lt_of_le_of_lt (Nat.zero_le _) hdec
    have hqp : q'.toNat = q.toNat - 1 := toNat_pred64 hqpos
    have hrn : r'.toNat = r.toNat + dn1.toNat := toNat_add_digit r dn1 hr
    have hrlt : r'.toNat < base := UInt64.lt_iff_toNat_lt.mp hr'
    refine ih ?_ hrlt (by rw [hqp]; exact Nat.le_pred_of_lt hdec)
    obtain ⟨m, hm⟩ : ∃ m, q.toNat = m + 1 := ⟨q.toNat - 1, (Nat.succ_pred_eq_of_pos hqpos).symm⟩
    rw [hrn, hqp, hm]
    rw [hm] at hinv
    grind
  | case2 q r hfire q' r' hr' =>
    have hq := q_le_of_inv hinv hu2 hnorm
    have hdec : U / V < q.toNat := by
      rw [recheck_test_iff dn2 nu q r hq hr] at hfire
      rcases hfire with h | h
      · omega
      · exact KnuthD.div_lt_of_test hV hVpos hU hulow hinv h
    have hqpos : 0 < q.toNat := Nat.lt_of_le_of_lt (Nat.zero_le _) hdec
    have hqn : q'.toNat = q.toNat - 1 := toNat_pred64 hqpos
    have hrn : r'.toNat = r.toNat + dn1.toNat := toNat_add_digit r dn1 hr
    have hrbig : base ≤ r'.toNat := by
      have := mt UInt64.lt_iff_toNat_lt.mpr hr'
      simp only [show BASE.toNat = base from rfl] at this
      omega
    have hinv' : u2 = q'.toNat * dn1.toNat + r'.toNat := by
      obtain ⟨m, hm⟩ : ∃ m, q.toNat = m + 1 := ⟨q.toNat - 1, (Nat.succ_pred_eq_of_pos hqpos).symm⟩
      rw [hqn, hrn, hm]
      rw [hm] at hinv
      grind
    have hqsmall : q'.toNat < base := by
      refine Nat.lt_of_mul_lt_mul_right (a := dn1.toNat) ?_
      simp only [base_eq] at hu2 hrbig hinv' ⊢; omega
    refine ⟨hqsmall, by rw [hqn]; exact Nat.le_pred_of_lt hdec, ?_⟩
    refine KnuthD.le_succ_div_of_not_test hV hVpos hU hinv' hvrest hvtop1 hqsmall ?_
    calc q'.toNat * dn2.toNat ≤ (base - 1) * (base - 1) :=
          Nat.mul_le_mul (by omega) (by omega)
      _ ≤ base * r'.toNat := by
          have h1 : base * base ≤ base * r'.toNat := Nat.mul_le_mul_left _ hrbig
          simp only [base_eq] at h1 ⊢; omega
      _ ≤ base * r'.toNat + nu.toNat := Nat.le_add_right _ _
  | case3 q r hfail =>
    have hq := q_le_of_inv hinv hu2 hnorm
    have harith : ¬ (base ≤ q.toNat ∨ base * r.toNat + nu.toNat < q.toNat * dn2.toNat) := by
      rw [← recheck_test_iff dn2 nu q r hq hr]; simpa using hfail
    have hf1 : q.toNat < base := by omega
    have hf2 : q.toNat * dn2.toNat ≤ base * r.toNat + nu.toNat := by omega
    exact ⟨hf1, hle, KnuthD.le_succ_div_of_not_test hV hVpos hU hinv hvrest hvtop1 hf1 hf2⟩

end Nat.Big
