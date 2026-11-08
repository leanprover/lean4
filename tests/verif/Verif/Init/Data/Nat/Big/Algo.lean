module

import all Init.Data.ByteArray.Basic
import all Init.Data.ByteArray.Extra
import all Init.Data.UInt.Log2
import all Init.Data.Fin.Log2
public import Verif.Init.Data.Nat.Big.Bits

/-! Correctness of `pow`, `gcd` and `powMod`. -/

namespace Nat.Big

/-! ## Powers -/


public theorem shr1_toNat (e : USize) : (e >>> 1).toNat = e.toNat / 2 := by
  have e1 : (1 : USize).toNat % System.Platform.numBits = 1 := by
    rcases System.Platform.numBits_eq with h | h <;> simp [h]
  rw [USize.toNat_shiftRight, e1, Nat.shiftRight_eq_div_pow]

public theorem and1_iff (e : USize) : (e &&& 1 == 1) = true ↔ e.toNat % 2 = 1 := by
  have e1 : (1 : USize).toNat = 1 := by
    rcases System.Platform.numBits_eq with h | h <;> simp [USize.toNat_ofNat, h]
  have h2 : (e &&& 1).toNat = e.toNat % 2 := by
    rw [USize.toNat_and, e1, show (1 : Nat) = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  constructor
  · intro h
    have := congrArg USize.toNat (beq_iff_eq.mp h)
    rw [h2, e1] at this; exact this
  · intro h
    apply beq_iff_eq.mpr
    apply USize.toNat_inj.mp
    rw [h2, e1, h]

public theorem powAcc_spec (base acc : Mag) (e : USize) (hb : base.IsNorm) (hacc : acc.IsNorm)
    (_he0 : e.toNat ≠ 0) (hfit : (acc.n + base.n * e.toNat + 1) * 4 ≤ maxBytes) :
    (if (e &&& 1 == 1) = true then mul acc base else acc).val = acc.val * base.val ^ (e.toNat % 2) ∧
      (if (e &&& 1 == 1) = true then mul acc base else acc).IsNorm ∧
      (if (e &&& 1 == 1) = true then mul acc base else acc).n ≤ acc.n + base.n * (e.toNat % 2) := by
  split
  · next ho =>
    have ho' := (and1_iff e).mp ho
    obtain ⟨v, nm⟩ := val_mul acc base hacc hb (by
      have : base.n ≤ base.n * e.toNat := Nat.le_mul_of_pos_right _ (by omega)
      omega)
    refine ⟨by rw [v, ho', Nat.pow_one], nm, ?_⟩
    rw [ho', Nat.mul_one]; exact n_le_of_mul _ _ _ nm v
  · next ho =>
    have ho' : e.toNat % 2 = 0 := by
      have := mt (and1_iff e).mpr ho; omega
    rw [ho']; simp [hacc]

public theorem powLoop_spec (base : Mag) (e : USize) (acc : Mag) (hb : base.IsNorm) (hacc : acc.IsNorm)
    (hfit : (acc.n + base.n * e.toNat + 1) * 4 ≤ maxBytes) :
    (powLoop base e acc).val = acc.val * base.val ^ e.toNat ∧ (powLoop base e acc).IsNorm := by
  fun_induction powLoop base e acc with
  | case1 base acc => simp [hacc]
  | case2 base e acc h acc' h1 =>
    have he0 : e.toNat ≠ 0 := fun h' => h (USize.toNat_inj.mp (by simpa using h'))
    have he1 : e.toNat = 1 := by simpa using congrArg USize.toNat (beq_iff_eq.mp h1)
    obtain ⟨v, nm, -⟩ : acc'.val = acc.val * base.val ^ (e.toNat % 2) ∧ acc'.IsNorm ∧
        acc'.n ≤ acc.n + base.n * (e.toNat % 2) := powAcc_spec base acc e hb hacc he0 hfit
    rw [he1] at v
    exact ⟨by rw [he1]; exact v, nm⟩
  | case3 base e acc h acc' h1 ih =>
    have he0 : e.toNat ≠ 0 := fun h' => h (USize.toNat_inj.mp (by simpa using h'))
    have he1 : e.toNat ≠ 1 := fun h' => h1 (beq_iff_eq.mpr (USize.toNat_inj.mp (by simpa using h')))
    obtain ⟨v, nm, sa⟩ : acc'.val = acc.val * base.val ^ (e.toNat % 2) ∧ acc'.IsNorm ∧
        acc'.n ≤ acc.n + base.n * (e.toNat % 2) := powAcc_spec base acc e hb hacc he0 hfit
    have hsplit : base.n * e.toNat = base.n * (e.toNat % 2) + 2 * (base.n * (e.toNat / 2)) := by
      conv => lhs; rw [← Nat.mod_add_div e.toNat 2]
      rw [Nat.mul_add, Nat.mul_left_comm]
    have hq : 1 ≤ e.toNat / 2 := by omega
    have hbb : base.n * 2 ≤ base.n * e.toNat := Nat.mul_le_mul_left _ (by omega)
    obtain ⟨vb, nb⟩ := val_mul base base hb hb (by omega)
    have sb := n_le_of_mul _ _ _ nb vb
    have hmono : (mul base base).n * (e.toNat / 2) ≤ 2 * (base.n * (e.toNat / 2)) := by
      rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ (by omega)
    obtain ⟨v', n'⟩ := ih nb nm (by rw [shr1_toNat]; omega)
    refine ⟨?_, n'⟩
    rw [v', v, vb, shr1_toNat, Nat.mul_assoc, ← Nat.pow_two, ← Nat.pow_mul, ← Nat.pow_add,
      Nat.mod_add_div]

/-- `pow` computes `a ^ e` unless the result could exceed `maxBytes`. -/
public theorem pow_spec (a : Mag) (e : USize) (ha : a.IsNorm) (hfit : (a.n * e.toNat + 2) * 4 ≤ maxBytes) :
    (pow a e).val = a.val ^ e.toNat ∧ (pow a e).IsNorm := by
  obtain ⟨v1, n1⟩ := val_one
  have s1 : (ofUInt64 1).n ≤ 1 := (ofUInt64 1).n_le_of_val_lt n1 1 (by rw [v1]; decide)
  obtain ⟨v, nm⟩ := powLoop_spec a e (ofUInt64 1) ha n1 (by omega)
  exact ⟨by rw [pow, v, v1, Nat.one_mul], nm⟩


/-! ## Greatest common divisor -/

/-- A remainder is less than half of the dividend. -/
public theorem two_mul_mod_lt (x y : Nat) (hy : 0 < y) (hyx : y ≤ x) : 2 * (x % y) < x := by
  have h1 := Nat.mod_lt x hy
  rcases Nat.lt_or_ge x (2 * y) with h | h
  · have : x % y = x - y := by
      rw [Nat.mod_eq_sub_mod hyx, Nat.mod_eq_of_lt (by omega)]
    omega
  · omega

public theorem gcdLoop_spec (k : Nat) : ∀ (fuel : Nat) (a b : Mag), a.IsNorm → b.IsNorm →
    (max a.n b.n + 3) * 4 ≤ maxBytes → b.val ≤ a.val → b.val < 2 ^ k → 2 * k + 1 ≤ fuel →
    (gcdLoop fuel a b).val = Nat.gcd a.val b.val ∧ (gcdLoop fuel a b).IsNorm := by
  induction k with
  | zero =>
    intro fuel a b ha hb hfit hle hlt hf
    have hb0 : b.val = 0 := by simpa using hlt
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have : b.usize = 0 := by
      have := b.n_le_of_val_lt hb 0 (by rw [hb0]; decide)
      exact USize.toNat_inj.mp (by rw [b.usize_toNat]; simp; omega)
    simp only [gcdLoop, this, beq_self_eq_true, ite_true]
    exact ⟨by rw [hb0, Nat.gcd_zero_right], ha⟩
  | succ k ih =>
    intro fuel a b ha hb hfit hle hlt hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    simp only [gcdLoop]
    split
    · next h =>
      have : b.n = 0 := by
        have := b.usize_toNat; rw [beq_iff_eq.mp h] at this; simpa using this.symm
      have hv : b.val = 0 := by rw [Mag.val, this]; rfl
      exact ⟨by rw [hv, Nat.gcd_zero_right], ha⟩
    · next h =>
      have hbn : 0 < b.n := by
        have : b.usize.toNat ≠ 0 :=
          fun h' => h (beq_iff_eq.mpr (USize.toNat_inj.mp (by simpa using h')))
        rw [b.usize_toNat] at this; omega
      have hbpos : 0 < b.val := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) (b.pow_le_val hb hbn)
      obtain ⟨-, vr, -, nr⟩ := divMod_spec a b ha hb (by omega)
      have hrl : (divMod a b).2.val < b.val := by rw [vr]; exact Nat.mod_lt _ hbpos
      have sr : (divMod a b).2.n ≤ b.n := (divMod a b).2.n_le_of_val_lt nr _
        (Nat.lt_of_lt_of_le hrl (Nat.le_of_lt b.val_lt))
      have hg : Nat.gcd a.val b.val = Nat.gcd b.val (divMod a b).2.val := by
        rw [vr, Nat.gcd_comm b.val, ← Nat.gcd_rec, Nat.gcd_comm]
      rw [hg]
      -- one more step: the remainder after two steps is below half of `b`
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      simp only [gcdLoop]
      split
      · next h' =>
        have : (divMod a b).2.n = 0 := by
          have := (divMod a b).2.usize_toNat; rw [beq_iff_eq.mp h'] at this; simpa using this.symm
        have hv : (divMod a b).2.val = 0 := by rw [Mag.val, this]; rfl
        exact ⟨by rw [hv, Nat.gcd_zero_right], hb⟩
      · next h' =>
        generalize (divMod a b).2 = r at *
        have hrn : 0 < r.n := by
          have : r.usize.toNat ≠ 0 :=
            fun h'' => h' (beq_iff_eq.mpr (USize.toNat_inj.mp (by simpa using h'')))
          rw [r.usize_toNat] at this; omega
        have hrpos : 0 < r.val := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) (r.pow_le_val nr hrn)
        obtain ⟨-, vs, -, ns⟩ := divMod_spec b r hb nr (by omega)
        have hsl : (divMod b r).2.val < r.val := by rw [vs]; exact Nat.mod_lt _ hrpos
        have hhalf : 2 * (divMod b r).2.val < b.val := by
          rw [vs]; exact two_mul_mod_lt _ _ hrpos (Nat.le_of_lt hrl)
        have ss : (divMod b r).2.n ≤ r.n := (divMod b r).2.n_le_of_val_lt ns _
          (Nat.lt_of_lt_of_le hsl (Nat.le_of_lt r.val_lt))
        have hg' : Nat.gcd b.val r.val = Nat.gcd r.val (divMod b r).2.val := by
          rw [vs, Nat.gcd_comm r.val, ← Nat.gcd_rec, Nat.gcd_comm]
        rw [hg']
        exact ih f' r (divMod b r).2 nr ns (by omega) (Nat.le_of_lt hsl)
          (by rw [Nat.pow_succ] at hlt; omega) (by omega)

/-- `gcd` computes `Nat.gcd`. -/
public theorem gcd_spec (a b : Mag) (ha : a.IsNorm) (hb : b.IsNorm)
    (hfit : (max a.n b.n + 3) * 4 ≤ maxBytes) :
    (gcd a b).val = Nat.gcd a.val b.val ∧ (gcd a b).IsNorm := by
  unfold gcd
  rcases Nat.le_total b.val a.val with hle | hle
  · exact gcdLoop_spec (32 * b.n) (64 * (a.n + b.n) + 2) a b ha hb hfit hle b.val_lt (by omega)
  · -- the first step swaps the operands
    simp only [gcdLoop]
    split
    · next h =>
      have : b.n = 0 := by
        have := b.usize_toNat; rw [beq_iff_eq.mp h] at this; simpa using this.symm
      have hv : b.val = 0 := by rw [Mag.val, this]; rfl
      exact ⟨by rw [hv, Nat.gcd_zero_right], ha⟩
    · next h =>
      have hbn : 0 < b.n := by
        have : b.usize.toNat ≠ 0 :=
          fun h' => h (beq_iff_eq.mpr (USize.toNat_inj.mp (by simpa using h')))
        rw [b.usize_toNat] at this; omega
      have hbpos : 0 < b.val := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) (b.pow_le_val hb hbn)
      obtain ⟨-, vr, -, nr⟩ := divMod_spec a b ha hb (by omega)
      have hrl : (divMod a b).2.val < b.val := by rw [vr]; exact Nat.mod_lt _ hbpos
      have hra : (divMod a b).2.val ≤ a.val := by rw [vr]; exact Nat.mod_le _ _
      have sr : (divMod a b).2.n ≤ a.n := (divMod a b).2.n_le_of_val_lt nr _
        (Nat.lt_of_le_of_lt hra a.val_lt)
      have hg : Nat.gcd a.val b.val = Nat.gcd b.val (divMod a b).2.val := by
        rw [vr, Nat.gcd_comm b.val, ← Nat.gcd_rec, Nat.gcd_comm]
      rw [hg]
      exact gcdLoop_spec (32 * a.n) (64 * (a.n + b.n) + 1) b _ hb nr (by omega) (Nat.le_of_lt hrl)
        (Nat.lt_of_le_of_lt hra a.val_lt) (by omega)

/-! ## Modular powers -/


public theorem bit_iff (e : Mag) (i : USize) :
    (((getOr0 e (i >>> 5) >>> (i &&& 31).toUInt32) &&& 1) == 1) = true ↔ e.val.testBit i.toNat := by
  have h1 : ((getOr0 e (i >>> 5) >>> (i &&& 31).toUInt32) &&& 1).toNat =
      e.digit (i.toNat / 32) / 2 ^ (i.toNat % 32) % 2 := by
    rw [UInt32.toNat_and, UInt32.toNat_shiftRight, getOr0_toNat, shiftRight5_toNat, and31_toNat,
      show (i.toNat % 32) % 32 = i.toNat % 32 by omega, Nat.shiftRight_eq_div_pow]
    rw [UInt32.toNat_one, Nat.and_one_is_mod]
  rw [Mag.testBit_val, Nat.testBit_eq_decide_div_mod_eq]
  constructor
  · intro h
    have := congrArg UInt32.toNat (beq_iff_eq.mp h)
    rw [h1] at this; simpa using this
  · intro h
    apply beq_iff_eq.mpr; apply UInt32.toNat_inj.mp
    rw [h1]; simpa using h


public theorem mulMod_spec (x y m : Mag) (hx : x.IsNorm) (hy : y.IsNorm) (hm : m.IsNorm)
    (hxl : x.val < m.val) (hyl : y.val < m.val) (hfit : (2 * m.n + 3) * 4 ≤ maxBytes) :
    (divMod (mul x y) m).2.val = x.val * y.val % m.val ∧ (divMod (mul x y) m).2.IsNorm ∧
      (divMod (mul x y) m).2.val < m.val := by
  have hmpos : 0 < m.val := by omega
  have sx := x.n_le_of_val_lt hx _ (Nat.lt_of_lt_of_le hxl (Nat.le_of_lt m.val_lt))
  have sy := y.n_le_of_val_lt hy _ (Nat.lt_of_lt_of_le hyl (Nat.le_of_lt m.val_lt))
  obtain ⟨vp, np⟩ := val_mul x y hx hy (by omega)
  have sp := n_le_of_mul _ _ _ np vp
  obtain ⟨-, vr, -, nr⟩ := divMod_spec (mul x y) m np hm (by omega)
  exact ⟨by rw [vr, vp], nr, by rw [vr]; exact Nat.mod_lt _ hmpos⟩

public theorem powModLoop_spec (e m : Mag) (hm : m.IsNorm) (hm1 : 1 < m.val) (A : Nat)
    (hfit : (2 * m.n + 3) * 4 ≤ maxBytes) (nbits : USize) (hnb : e.val < 2 ^ nbits.toNat)
    (i : USize) (base acc : Mag) (hb : base.IsNorm) (hacc : acc.IsNorm) (hi : i.toNat ≤ nbits.toNat)
    (hbase : i.toNat < nbits.toNat → base.val = A ^ (2 ^ i.toNat) % m.val)
    (hbl : base.val < m.val) (hav : acc.val = A ^ (e.val % 2 ^ i.toNat) % m.val) :
    (powModLoop e m nbits i base acc).val = A ^ e.val % m.val ∧
      (powModLoop e m nbits i base acc).IsNorm := by
  have hmpos : 0 < m.val := by omega
  fun_induction powModLoop e m nbits i base acc with
  | case1 i base acc h bit acc' base' ih =>
    have hlt := USize.lt_iff_toNat_lt.mp h
    have hsucc : (i + 1).toNat = i.toNat + 1 := toNat_succ_of_lt_size (by
      have := nbits.toNat_lt_size; omega)
    have hbv := hbase hlt
    have hal : acc.val < m.val := by rw [hav]; exact Nat.mod_lt _ hmpos
    have hsplit : e.val % 2 ^ (i.toNat + 1) =
        e.val % 2 ^ i.toNat + 2 ^ i.toNat * (e.val / 2 ^ i.toNat % 2) := by
      rw [Nat.pow_succ, Nat.mod_mul]
    obtain ⟨va', na', la'⟩ : acc'.val = A ^ (e.val % 2 ^ (i.toNat + 1)) % m.val ∧ acc'.IsNorm ∧
        acc'.val < m.val := by
      simp only [acc']
      split
      · next hbit =>
        have ht := (bit_iff e i).mp hbit
        rw [Nat.testBit_eq_decide_div_mod_eq] at ht
        have ht' : e.val / 2 ^ i.toNat % 2 = 1 := by simpa using ht
        obtain ⟨v, n, l⟩ := mulMod_spec acc base m hacc hb hm hal hbl hfit
        refine ⟨?_, n, l⟩
        rw [v, hav, hbv, ← Nat.mul_mod, ← Nat.pow_add, hsplit, ht', Nat.mul_one]
      · next hbit =>
        have ht : e.val / 2 ^ i.toNat % 2 = 0 := by
          have h1 := mt (bit_iff e i).mpr hbit
          rw [Nat.testBit_eq_decide_div_mod_eq] at h1
          have : ¬ e.val / 2 ^ i.toNat % 2 = 1 := by simpa using h1
          omega
        refine ⟨?_, hacc, hal⟩
        rw [hav, hsplit, ht, Nat.mul_zero, Nat.add_zero]
    obtain ⟨vb', nb', lb'⟩ : (i.toNat + 1 < nbits.toNat → base'.val = A ^ (2 ^ (i.toNat + 1)) % m.val) ∧
        base'.IsNorm ∧ base'.val < m.val := by
      simp only [base']
      split
      · next hn =>
        obtain ⟨v, n, l⟩ := mulMod_spec base base m hb hb hm hbl hbl hfit
        refine ⟨fun _ => ?_, n, l⟩
        rw [v, hbv, ← Nat.mul_mod, ← Nat.pow_add, Nat.pow_succ 2, Nat.mul_two]
      · next hn =>
        refine ⟨fun h' => absurd (USize.lt_iff_toNat_lt.mpr (by rw [hsucc]; exact h')) hn, hb, hbl⟩
    exact ih nb' na' (by rw [hsucc]; omega) (by rw [hsucc]; exact vb') lb' (by rw [hsucc]; exact va')
  | case2 i base acc h =>
    have hge := not_lt_toNat h
    rw [hav, show i.toNat = nbits.toNat by omega, Nat.mod_eq_of_lt hnb]
    exact ⟨rfl, hacc⟩

/-- `powMod` computes `a ^ e % m` for `m > 1`. -/
public theorem powMod_spec (a e m : Mag) (ha : a.IsNorm) (he : e.IsNorm) (hm : m.IsNorm) (hm1 : 1 < m.val)
    (hfit : (max a.n (2 * m.n) + 3) * 4 ≤ maxBytes) :
    (powMod a e m).val = a.val ^ e.val % m.val ∧ (powMod a e m).IsNorm := by
  obtain ⟨v1, n1⟩ := val_one
  have hmpos : 0 < m.val := by omega
  unfold powMod
  split
  · next h =>
    have : e.n = 0 := by
      have := e.usize_toNat; rw [beq_iff_eq.mp h] at this; simpa using this.symm
    have hv : e.val = 0 := by rw [Mag.val, this]; rfl
    exact ⟨by rw [v1, hv, Nat.pow_zero, Nat.mod_eq_of_lt hm1], n1⟩
  · next h =>
    have hen : 0 < e.n := by
      have : e.usize.toNat ≠ 0 := fun h' => h (beq_iff_eq.mpr (USize.toNat_inj.mp (by simpa using h')))
      rw [e.usize_toNat] at this; omega
    have hev : e.val ≠ 0 := by
      have := e.pow_le_val he hen; have := Nat.two_pow_pos (32 * (e.n - 1)); omega
    have hl := log2_spec e he
    have hlb : Nat.log2 e.val < 32 * e.n := (Nat.log2_lt hev).mpr e.val_lt
    have hnb : (log2 e + 1).toNat = Nat.log2 e.val + 1 := by
      rw [toNat_succ_of_lt_size (by have := e.n_mul_32_lt; omega), hl]
    obtain ⟨-, vr, -, nr⟩ := divMod_spec a m ha hm (by omega)
    have hrl : (divMod a m).2.val < m.val := by rw [vr]; exact Nat.mod_lt _ hmpos
    refine powModLoop_spec e m hm hm1 a.val (by omega) _ (by rw [hnb]; exact Nat.lt_log2_self) 0 _ _
      nr n1 (by simp) (fun _ => by rw [vr]; simp) hrl ?_
    rw [v1, USize.toNat_zero, Nat.pow_zero, Nat.mod_one, Nat.pow_zero, Nat.mod_eq_of_lt hm1]

end Nat.Big
