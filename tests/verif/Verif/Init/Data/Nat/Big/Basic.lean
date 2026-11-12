module

import all Init.Data.ByteArray.Basic
import all Init.Data.ByteArray.Extra
import all Init.Data.UInt.Log2
import all Init.Data.Fin.Log2
public import Init.Data.Nat.Big

/-! The value of a magnitude and the correctness of addition, subtraction, comparison, schoolbook multiplication, shifts, bitwise operations and single-digit operations. -/

namespace ByteArray

/-- The little-endian 32-bit value at byte offset `i`, reading bytes past the end as `0`. -/
@[expose] public def readU32 (a : ByteArray) (i : Nat) : UInt32 :=
  a[i]!.toUInt32 ||| a[i + 1]!.toUInt32 <<< 8 ||| a[i + 2]!.toUInt32 <<< 16 |||
    a[i + 3]!.toUInt32 <<< 24

public theorem ugetUInt32LE_eq (a : ByteArray) (i : USize) (h) :
    a.ugetUInt32LE i h = a.readU32 i.toNat := by
  have h0 : i.toNat < a.size := by omega
  have h1 : i.toNat + 1 < a.size := by omega
  have h2 : i.toNat + 2 < a.size := by omega
  have h3 : i.toNat + 3 < a.size := by omega
  simp [ugetUInt32LE, readU32, getElem!_pos, h0, h1, h2, h3]

public theorem or_shift_eq_add (a b i : Nat) (hb : b < 2 ^ i) : a * 2 ^ i ||| b = a * 2 ^ i + b := by
  rw [← Nat.shiftLeft_eq, Nat.shiftLeft_add_eq_or_of_lt hb]


public theorem combine_bytes (v : UInt32) :
    (v.toUInt8.toUInt32 ||| (v >>> 8).toUInt8.toUInt32 <<< 8 |||
      (v >>> 16).toUInt8.toUInt32 <<< 16 ||| (v >>> 24).toUInt8.toUInt32 <<< 24) = v := by
  apply UInt32.toNat_inj.mp
  have hv := v.toNat_lt
  simp only [UInt32.toNat_or, UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32, UInt32.toNat_toUInt8,
    UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
    show (8 : UInt32).toNat % 32 = 8 from rfl, show (16 : UInt32).toNat % 32 = 16 from rfl,
    show (24 : UInt32).toNat % 32 = 24 from rfl]
  generalize v.toNat = n at *
  have e1 : (n / 2 ^ 8 % 256 * 2 ^ 8) % 2 ^ 32 = n / 2 ^ 8 % 256 * 2 ^ 8 := Nat.mod_eq_of_lt (by omega)
  have e2 : (n / 2 ^ 16 % 256 * 2 ^ 16) % 2 ^ 32 = n / 2 ^ 16 % 256 * 2 ^ 16 :=
    Nat.mod_eq_of_lt (by omega)
  have e3 : (n / 2 ^ 24 % 256 * 2 ^ 24) % 2 ^ 32 = n / 2 ^ 24 % 256 * 2 ^ 24 :=
    Nat.mod_eq_of_lt (by omega)
  rw [e1, e2, e3, Nat.or_comm (n % 2 ^ 8), or_shift_eq_add _ _ 8 (by omega),
    Nat.or_comm (n / 2 ^ 8 % 256 * 2 ^ 8 + n % 2 ^ 8), or_shift_eq_add _ _ 16 (by omega),
    Nat.or_comm (n / 2 ^ 16 % 256 * 2 ^ 16 + (n / 2 ^ 8 % 256 * 2 ^ 8 + n % 2 ^ 8)),
    or_shift_eq_add _ _ 24 (by omega)]
  omega

public theorem readU32_usetUInt32LE_self (a : ByteArray) (i : USize) (v : UInt32) (h) :
    (a.usetUInt32LE i v h).readU32 i.toNat = v := by
  simp only [usetUInt32LE, readU32]
  simp (disch := first | omega | (simp only [ByteArray.size_set!]; omega)) only
    [getElem!_set!_ne, getElem!_set!_self]
  exact combine_bytes v

public theorem readU32_usetUInt32LE_of_disjoint (a : ByteArray) (i : USize) (v : UInt32) (h) (j : Nat)
    (hij : j + 4 ≤ i.toNat ∨ i.toNat + 4 ≤ j) :
    (a.usetUInt32LE i v h).readU32 j = a.readU32 j := by
  simp only [usetUInt32LE, readU32]
  simp (disch := omega) only [getElem!_set!_ne]

end ByteArray

namespace Nat.Big
namespace Mag

/-! ## Digit model -/

/-- The value of digit `j` (`0` past the end). -/
@[expose] public def digit (a : Mag) (j : Nat) : Nat := (a.bytes.readU32 (j * 4)).toNat

/-- The value of the low `k` digits. -/
@[expose] public def valUpTo (a : Mag) : Nat → Nat
  | 0 => 0
  | k + 1 => a.valUpTo k + a.digit k * 2 ^ (32 * k)

/-- The value of a magnitude. -/
@[expose] public def val (a : Mag) : Nat := a.valUpTo a.n

/-- No leading zero digit. -/
@[expose] public def IsNorm (a : Mag) : Prop := a.n = 0 ∨ a.digit (a.n - 1) ≠ 0

public theorem digit_lt (a : Mag) (j : Nat) : a.digit j < 2 ^ 32 := (a.bytes.readU32 (j * 4)).toNat_lt

public theorem get_toNat (a : Mag) (i : USize) (h : i.toNat < a.n) : (a.get i h).toNat = a.digit i.toNat := by
  simp only [get, digit, ByteArray.ugetUInt32LE_eq, offset_toNat h]

public theorem digit_set (a : Mag) (i : USize) (h : i.toNat < a.n) (v : UInt32) (j : Nat) :
    (a.set i h v).digit j = if j = i.toNat then v.toNat else a.digit j := by
  simp only [set, digit]
  have ho := offset_toNat h
  split
  · next hj => subst hj; rw [← ho, ByteArray.readU32_usetUInt32LE_self]
  · next hj =>
    rw [ByteArray.readU32_usetUInt32LE_of_disjoint _ _ _ _ _ (by rw [ho]; omega)]

public theorem getElem!_replicate (k : Nat) (x : Nat) : (ByteArray.replicate k 0)[x]! = 0 := by
  by_cases hx : x < (ByteArray.replicate k 0).size
  · rw [getElem!_pos (ByteArray.replicate k 0) x hx]
    simp [ByteArray.replicate, ByteArray.getElem_eq_getElem_data]
  · rw [getElem!_neg (ByteArray.replicate k 0) x hx]; rfl

public theorem digit_zeros (k : USize) (h) (j : Nat) : (zeros k h).digit j = 0 := by
  simp [zeros, digit, ByteArray.readU32, getElem!_replicate]

public theorem valUpTo_congr {a b : Mag} {k : Nat} (h : ∀ j, j < k → a.digit j = b.digit j) :
    a.valUpTo k = b.valUpTo k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [valUpTo, ih (fun j hj => h j (by omega)), h k (by omega)]

public theorem valUpTo_set_of_le (a : Mag) (i : USize) (h) (v : UInt32) (k : Nat) (hk : k ≤ i.toNat) :
    (a.set i h v).valUpTo k = a.valUpTo k :=
  valUpTo_congr fun j hj => by rw [digit_set]; simp; omega

public theorem valUpTo_set_succ (a : Mag) (i : USize) (h) (v : UInt32) :
    (a.set i h v).valUpTo (i.toNat + 1) = a.valUpTo i.toNat + v.toNat * 2 ^ (32 * i.toNat) := by
  rw [valUpTo, valUpTo_set_of_le _ _ _ _ _ (Nat.le_refl _), digit_set]; simp

public theorem digit_of_n_le (a : Mag) (j : Nat) (hj : a.n ≤ j) : a.digit j = 0 := by
  have := a.n_mul_four
  simp only [digit, ByteArray.readU32]
  rw [getElem!_neg _ _ (by omega), getElem!_neg _ _ (by omega), getElem!_neg _ _ (by omega),
    getElem!_neg _ _ (by omega)]
  rfl

public theorem valUpTo_of_n_le (a : Mag) (k : Nat) (hk : a.n ≤ k) : a.valUpTo k = a.val := by
  induction k with
  | zero => simp [val, show a.n = 0 by omega, valUpTo]
  | succ k ih =>
    by_cases hk' : a.n ≤ k
    · rw [valUpTo, ih hk', digit_of_n_le _ _ hk']; simp
    · rw [show k + 1 = a.n by omega]; rfl

public theorem valUpTo_lt (a : Mag) (k : Nat) : a.valUpTo k < 2 ^ (32 * k) := by
  induction k with
  | zero => simp [valUpTo]
  | succ k ih =>
    have := a.digit_lt k
    rw [valUpTo, show 32 * (k + 1) = 32 * k + 32 by omega, Nat.pow_add]
    generalize (2 : Nat) ^ (32 * k) = X at ih ⊢
    have : a.digit k * X ≤ (2 ^ 32 - 1) * X := Nat.mul_le_mul_right _ (by omega)
    grind

public theorem val_lt (a : Mag) : a.val < 2 ^ (32 * a.n) := a.valUpTo_lt a.n

/-! ## `take` and `normalize` -/

public theorem getElem!_shrink (b : ByteArray) (m x : Nat) (hx : x < m) : (b.shrink m)[x]! = b[x]! := by
  by_cases h : x < b.size
  · rw [getElem!_pos (b.shrink m) x (by rw [size_shrink]; omega), getElem!_pos b x h]
    simp [ByteArray.shrink, ByteArray.getElem_extract]
  · rw [getElem!_neg (b.shrink m) x (by rw [size_shrink]; omega), getElem!_neg b x h]

public theorem digit_take (a : Mag) (k : USize) (hk) (j : Nat) :
    (a.take k hk).digit j = if j < k.toNat then a.digit j else 0 := by
  split
  · next hj =>
    simp only [take, digit, ByteArray.readU32]
    rw [getElem!_shrink _ _ _ (by omega), getElem!_shrink _ _ _ (by omega),
      getElem!_shrink _ _ _ (by omega), getElem!_shrink _ _ _ (by omega)]
  · next hj => exact digit_of_n_le _ _ (by simp; omega)


public theorem topNonzero_spec (a : Mag) (k : USize) (hk) :
    (∀ j, (a.topNonzero k hk).toNat ≤ j → j < k.toNat → a.digit j = 0) ∧
      ((a.topNonzero k hk).toNat = 0 ∨ a.digit ((a.topNonzero k hk).toNat - 1) ≠ 0) := by
  fun_induction topNonzero a k hk with
  | case1 k hk h hz ih =>
    rw [toNat_pred h] at ih
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨fun j hj1 hj2 => ?_, ih2⟩
    by_cases hj : j = k.toNat - 1
    · subst hj
      have := (get_toNat a (k - 1) (by rw [toNat_pred h]; omega)).trans
        (congrArg a.digit (toNat_pred h))
      rw [← this]; simp at hz; simp [hz]
    · exact ih1 j hj1 (by omega)
  | case2 k hk h hz =>
    refine ⟨fun j hj1 hj2 => by omega, Or.inr ?_⟩
    have := (get_toNat a (k - 1) (by rw [toNat_pred h]; omega)).trans
      (congrArg a.digit (toNat_pred h))
    rw [← this]; intro h0; apply hz; simpa [← UInt32.toNat_inj] using h0
  | case3 k hk h => exact ⟨fun j hj1 hj2 => by omega, Or.inl (by omega)⟩

public theorem valUpTo_eq_of_zero (a : Mag) (m k : Nat) (hmk : m ≤ k)
    (hz : ∀ j, m ≤ j → j < k → a.digit j = 0) : a.valUpTo k = a.valUpTo m := by
  induction k with
  | zero => rw [show m = 0 by omega]
  | succ k ih =>
    by_cases h : m ≤ k
    · rw [valUpTo, hz k h (by omega), ih h (fun j h1 h2 => hz j h1 (by omega))]; simp
    · rw [show m = k + 1 by omega]

public theorem val_take (a : Mag) (k : USize) (hk) : (a.take k hk).val = a.valUpTo k.toNat := by
  simp only [val, n_take]
  exact valUpTo_congr fun j hj => by rw [digit_take]; simp [hj]

public theorem val_normalize (a : Mag) : a.normalize.val = a.val := by
  simp only [normalize]
  rw [val_take]
  obtain ⟨h1, -⟩ := a.topNonzero_spec a.usize a.usize_le
  rw [usize_toNat] at h1
  have := a.topNonzero_usize_le
  rw [val, valUpTo_eq_of_zero a _ a.n this h1]

public theorem isNorm_take (a : Mag) (m : USize) (hm)
    (h2 : m.toNat = 0 ∨ a.digit (m.toNat - 1) ≠ 0) : (a.take m hm).IsNorm := by
  simp only [IsNorm, n_take]
  by_cases h0 : m.toNat = 0
  · exact Or.inl h0
  · refine Or.inr ?_
    rw [digit_take, ite_eq_left (by omega)]
    exact h2.resolve_left h0

public theorem isNorm_normalize (a : Mag) : a.normalize.IsNorm :=
  isNorm_take _ _ _ (a.topNonzero_spec a.usize a.usize_le).2

end Mag

open Mag

/-! ## Addition -/

public theorem addTail_spec (a : Mag) (la i : USize) (hla) (k : UInt64) (c : Mag) (hc) (hi)
    (hk : k.toNat < 2) (S : Nat)
    (hinv : c.valUpTo i.toNat + k.toNat * 2 ^ (32 * i.toNat) = a.valUpTo i.toNat + S) :
    (addTail a la i hla k c hc hi).valUpTo (la.toNat + 1) = a.val + S ∧
      (addTail a la i hla k c hc hi).n = c.n := by
  fun_induction addTail a la i hla k c hc hi with
  | case1 i k c hc hi h hi' t ih =>
    have hd := a.digit_lt i.toNat
    have hlt := USize.lt_iff_toNat_lt.mp h
    have hg : (a.get i (by omega)).toNat = a.digit i.toNat := get_toNat _ _ _
    have hglt := (a.get i (by omega)).toNat_lt
    have ht : t.toNat = a.digit i.toNat + k.toNat := by
      simp only [t, UInt64.toNat_add, UInt32.toNat_toUInt64]
      rw [hg] at hglt ⊢
      have : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
      omega
    have hcarry : (t >>> 32).toNat = t.toNat / 2 ^ 32 := by
      simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    have hv : t.toUInt32.toNat = t.toNat % 2 ^ 32 := by simp
    obtain ⟨ih1, ih2⟩ := ih (by rw [hcarry, ht]; omega) (by
      rw [toNat_succ_of_lt h, valUpTo_set_succ, valUpTo, hv, hcarry,
        show 32 * (i.toNat + 1) = 32 * i.toNat + 32 by omega, Nat.pow_add]
      generalize (2 : Nat) ^ (32 * i.toNat) = X at hinv ⊢
      have hdm := Nat.div_add_mod t.toNat (2 ^ 32)
      rw [ht] at hdm ⊢
      grind)
    exact ⟨ih1, by simp⟩
  | case2 i k c hc hi h =>
    have hle := not_lt_toNat h
    have heq : i.toNat = la.toNat := by omega
    refine ⟨?_, by simp⟩
    rw [← heq, valUpTo_set_succ]
    have : k.toUInt32.toNat = k.toNat := by simp; omega
    rw [this, hinv, ← valUpTo_of_n_le a i.toNat (by omega)]

public theorem addLoop_spec (a b : Mag) (la lb i : USize) (hla hlb hab) (k : UInt64) (c : Mag) (hc) (hi)
    (hk : k.toNat < 2)
    (hinv : c.valUpTo i.toNat + k.toNat * 2 ^ (32 * i.toNat) = a.valUpTo i.toNat + b.valUpTo i.toNat) :
    (addLoop a b la lb i hla hlb hab k c hc hi).valUpTo (la.toNat + 1) = a.val + b.val ∧
      (addLoop a b la lb i hla hlb hab k c hc hi).n = c.n := by
  fun_induction addLoop a b la lb i hla hlb hab k c hc hi with
  | case1 i k c hc hi h hi' t ih =>
    have hlt := USize.lt_iff_toNat_lt.mp h
    have hga : (a.get i (by omega)).toNat = a.digit i.toNat := get_toNat _ _ _
    have hgb : (b.get i (by omega)).toNat = b.digit i.toNat := get_toNat _ _ _
    have ha := (a.get i (by omega)).toNat_lt
    have hb := (b.get i (by omega)).toNat_lt
    have ht : t.toNat = a.digit i.toNat + b.digit i.toNat + k.toNat := by
      simp only [t, UInt64.toNat_add, UInt32.toNat_toUInt64]
      rw [hga, hgb] at *
      have : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
      omega
    have hcarry : (t >>> 32).toNat = t.toNat / 2 ^ 32 := by
      simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    have hv : t.toUInt32.toNat = t.toNat % 2 ^ 32 := by simp
    have hda := a.digit_lt i.toNat
    have hdb := b.digit_lt i.toNat
    obtain ⟨ih1, ih2⟩ := ih (by rw [hcarry, ht]; omega) (by
      rw [toNat_succ_of_lt h, valUpTo_set_succ, valUpTo, valUpTo, hv, hcarry,
        show 32 * (i.toNat + 1) = 32 * i.toNat + 32 by omega, Nat.pow_add]
      generalize (2 : Nat) ^ (32 * i.toNat) = X at hinv ⊢
      have hdm := Nat.div_add_mod t.toNat (2 ^ 32)
      rw [ht] at hdm ⊢
      grind)
    exact ⟨ih1, by simp⟩
  | case2 i k c hc hi h =>
    have hle := not_lt_toNat h
    rw [valUpTo_of_n_le b i.toNat (by omega)] at hinv
    exact addTail_spec a la i hla k c hc _ hk b.val hinv

public theorem val_addCore (a b : Mag) (hab h) : (addCore a b hab h).val = a.val + b.val := by
  obtain ⟨h1, h2⟩ := addLoop_spec a b a.usize b.usize 0 (usize_toNat a) (usize_toNat b) hab 0
    (zeros (a.usize + 1) (by rw [usize_succ_toNat]; exact h))
    (by rw [n_zeros, usize_succ_toNat]; omega) (by simp) (by simp) (by simp [valUpTo])
  simp only [usize_toNat] at h1
  simp only [addCore, val]
  rw [h2, n_zeros, usize_succ_toNat]
  exact h1

/-- `add` is correct unless the result exceeds `maxBytes`. -/
public theorem val_add (a b : Mag) (h : (max a.n b.n + 1) * 4 ≤ maxBytes) :
    (add a b).val = a.val + b.val ∧ (add a b).IsNorm := by
  unfold add
  split <;> split
  · exact ⟨by rw [val_normalize, val_addCore], isNorm_normalize _⟩
  · exfalso; omega
  · exact ⟨by rw [val_normalize, val_addCore, Nat.add_comm], isNorm_normalize _⟩
  · exfalso; omega


/-! ## Comparison -/

public theorem Mag.pow_le_val (a : Mag) (ha : a.IsNorm) (hn : 0 < a.n) : 2 ^ (32 * (a.n - 1)) ≤ a.val := by
  have hd : a.digit (a.n - 1) ≠ 0 := ha.resolve_left (by omega)
  rw [Mag.val, show a.n = (a.n - 1) + 1 by omega, Mag.valUpTo]
  rw [show a.n - 1 + 1 - 1 = a.n - 1 by omega]
  have : 1 * 2 ^ (32 * (a.n - 1)) ≤ a.digit (a.n - 1) * 2 ^ (32 * (a.n - 1)) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

public theorem compare_add_right' (x y c : Nat) : compare (x + c) (y + c) = compare x y := by
  rcases Nat.lt_trichotomy x y with h | h | h
  · rw [Nat.compare_eq_lt.mpr h, Nat.compare_eq_lt.mpr (by omega)]
  · subst h; rw [Nat.compare_eq_eq.mpr rfl, Nat.compare_eq_eq.mpr rfl]
  · rw [Nat.compare_eq_gt.mpr h, Nat.compare_eq_gt.mpr (by omega)]

public theorem cmpLoop_spec (a b : Mag) (i : USize) (ha hb) :
    cmpLoop a b i ha hb = compare (a.valUpTo i.toNat) (b.valUpTo i.toNat) := by
  fun_induction cmpLoop a b i ha hb with
  | case1 i ha hb h x y hxy hlt =>
    have hx : x.toNat = a.digit (i.toNat - 1) :=
      (Mag.get_toNat a (i - 1) _).trans (congrArg a.digit (toNat_pred h))
    have hy : y.toNat = b.digit (i.toNat - 1) :=
      (Mag.get_toNat b (i - 1) _).trans (congrArg b.digit (toNat_pred h))
    have hlt' : x.toNat < y.toNat := hlt
    rw [show i.toNat = (i.toNat - 1) + 1 by omega, Mag.valUpTo, Mag.valUpTo]
    have la := a.valUpTo_lt (i.toNat - 1)
    have lb := b.valUpTo_lt (i.toNat - 1)
    rw [hx, hy] at hlt'
    generalize (2 : Nat) ^ (32 * (i.toNat - 1)) = X at la lb ⊢
    have : (a.digit (i.toNat - 1) + 1) * X ≤ b.digit (i.toNat - 1) * X :=
      Nat.mul_le_mul_right _ (by omega)
    rw [Nat.compare_eq_lt.mpr (by grind)]
  | case2 i ha hb h x y hxy hlt =>
    have hx : x.toNat = a.digit (i.toNat - 1) :=
      (Mag.get_toNat a (i - 1) _).trans (congrArg a.digit (toNat_pred h))
    have hy : y.toNat = b.digit (i.toNat - 1) :=
      (Mag.get_toNat b (i - 1) _).trans (congrArg b.digit (toNat_pred h))
    have hne : x.toNat ≠ y.toNat := by simpa [← UInt32.toNat_inj] using hxy
    have hlt' : y.toNat < x.toNat := by have : ¬ x.toNat < y.toNat := hlt; omega
    rw [show i.toNat = (i.toNat - 1) + 1 by omega, Mag.valUpTo, Mag.valUpTo]
    have la := a.valUpTo_lt (i.toNat - 1)
    have lb := b.valUpTo_lt (i.toNat - 1)
    rw [hx, hy] at hlt'
    generalize (2 : Nat) ^ (32 * (i.toNat - 1)) = X at la lb ⊢
    have : (b.digit (i.toNat - 1) + 1) * X ≤ a.digit (i.toNat - 1) * X :=
      Nat.mul_le_mul_right _ (by omega)
    rw [Nat.compare_eq_gt.mpr (by grind)]
  | case3 i ha hb h x y hxy ih =>
    have hx : x.toNat = a.digit (i.toNat - 1) :=
      (Mag.get_toNat a (i - 1) _).trans (congrArg a.digit (toNat_pred h))
    have hy : y.toNat = b.digit (i.toNat - 1) :=
      (Mag.get_toNat b (i - 1) _).trans (congrArg b.digit (toNat_pred h))
    have heq : x.toNat = y.toNat := by simp at hxy; simp [hxy]
    rw [ih, toNat_pred h]
    conv => rhs; rw [show i.toNat = (i.toNat - 1) + 1 by omega, Mag.valUpTo, Mag.valUpTo]
    rw [← hx, ← hy, heq]
    exact (compare_add_right' _ _ _).symm
  | case4 i ha hb h => simp [show i.toNat = 0 by omega, Mag.valUpTo]

public theorem cmp_spec (a b : Mag) (ha : a.IsNorm) (hb : b.IsNorm) : cmp a b = compare a.val b.val := by
  unfold cmp
  dsimp only
  split
  · next h =>
    rw [cmpLoop_spec, Mag.usize_toNat]
    have : a.n = b.n := by
      have := congrArg USize.toNat h; simp only [Mag.usize_toNat] at this; exact this
    rw [Mag.valUpTo_of_n_le a _ (by omega), Mag.valUpTo_of_n_le b _ (by omega)]
  · next h =>
    have hne : a.n ≠ b.n := fun h' => h (USize.toNat_inj.mp (by simp only [Mag.usize_toNat, h']))
    split
    · next hlt =>
      have : a.n < b.n := by
        have := USize.lt_iff_toNat_lt.mp hlt; simpa only [Mag.usize_toNat] using this
      have h1 := a.val_lt
      have h2 := b.pow_le_val hb (by omega)
      have : 2 ^ (32 * a.n) ≤ 2 ^ (32 * (b.n - 1)) := Nat.pow_le_pow_right (by omega) (by omega)
      rw [Nat.compare_eq_lt.mpr (by omega)]
    · next hlt =>
      have : b.n < a.n := by
        have := not_lt_toNat hlt; simp only [Mag.usize_toNat] at this; omega
      have h1 := b.val_lt
      have h2 := a.pow_le_val ha (by omega)
      have : 2 ^ (32 * b.n) ≤ 2 ^ (32 * (a.n - 1)) := Nat.pow_le_pow_right (by omega) (by omega)
      rw [Nat.compare_eq_gt.mpr (by omega)]


/-! ## Subtraction -/

/-- One borrowing step: `x + k' 2^32 = y + k + s` for the stored digit `s` and new borrow `k'`. -/
public theorem sub_step (x y : UInt32) (k : UInt64) (hk : k.toNat < 2) :
    let t := x.toUInt64 - y.toUInt64 - k
    x.toNat + (t >>> 63).toNat * 2 ^ 32 = y.toNat + k.toNat + t.toUInt32.toNat ∧
      (t >>> 63).toNat < 2 := by
  intro t
  have := x.toNat_lt; have := y.toNat_lt
  have ht : t.toNat = (2 ^ 64 - k.toNat + (2 ^ 64 - y.toNat + x.toNat) % 2 ^ 64) % 2 ^ 64 := by
    simp [t, UInt64.toNat_sub, UInt32.toNat_toUInt64]
  have h1 : (t >>> 63).toNat = t.toNat / 2 ^ 63 := by
    simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  have h2 : t.toUInt32.toNat = t.toNat % 2 ^ 32 := by simp
  rw [h1, h2, ht]
  have : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  have : (2 : Nat) ^ 63 = 9223372036854775808 := rfl
  have : (2 : Nat) ^ 32 = 4294967296 := rfl
  omega

public theorem subTail_spec (a : Mag) (la i : USize) (hla) (k : UInt64) (c : Mag) (hc) (hi)
    (hk : k.toNat < 2) (S : Nat)
    (hinv : a.valUpTo i.toNat + k.toNat * 2 ^ (32 * i.toNat) = S + c.valUpTo i.toNat) :
    ∃ k' : Nat, k' < 2 ∧
      a.val + k' * 2 ^ (32 * la.toNat) = S + (subTail a la i hla k c hc hi).valUpTo la.toNat ∧
      (subTail a la i hla k c hc hi).n = c.n := by
  fun_induction subTail a la i hla k c hc hi with
  | case1 i k c hc hi h hi' t ih =>
    have hlt := USize.lt_iff_toNat_lt.mp h
    have hg : (a.get i (by omega)).toNat = a.digit i.toNat := Mag.get_toNat _ _ _
    -- the tail step is a borrow step with `y = 0`
    obtain ⟨hs1, hs2⟩ := sub_step (a.get i (by omega)) 0 k hk
    have ht : t = (a.get i (by omega)).toUInt64 - (0 : UInt32).toUInt64 - k := by simp [t]
    rw [← ht] at hs1 hs2
    simp only [UInt32.toNat_zero, Nat.zero_add, hg] at hs1
    obtain ⟨k', hk', h1, h2⟩ := ih hs2 (by
      rw [toNat_succ_of_lt h, Mag.valUpTo_set_succ, Mag.valUpTo,
        show 32 * (i.toNat + 1) = 32 * i.toNat + 32 by omega, Nat.pow_add]
      generalize (2 : Nat) ^ (32 * i.toNat) = X at hinv ⊢
      grind)
    exact ⟨k', hk', h1, by simpa using h2⟩
  | case2 i k c hc hi h =>
    have hle := not_lt_toNat h
    have heq : i.toNat = la.toNat := by omega
    refine ⟨k.toNat, hk, ?_, rfl⟩
    rw [← heq, ← Mag.valUpTo_of_n_le a i.toNat (by omega)]
    exact hinv

public theorem subLoop_spec (a b : Mag) (la lb i : USize) (hla hlb hab) (k : UInt64) (c : Mag) (hc) (hi)
    (hk : k.toNat < 2)
    (hinv : a.valUpTo i.toNat + k.toNat * 2 ^ (32 * i.toNat) = b.valUpTo i.toNat + c.valUpTo i.toNat) :
    ∃ k' : Nat, k' < 2 ∧
      a.val + k' * 2 ^ (32 * la.toNat) =
        b.val + (subLoop a b la lb i hla hlb hab k c hc hi).valUpTo la.toNat ∧
      (subLoop a b la lb i hla hlb hab k c hc hi).n = c.n := by
  fun_induction subLoop a b la lb i hla hlb hab k c hc hi with
  | case1 i k c hc hi h hi' t ih =>
    have hlt := USize.lt_iff_toNat_lt.mp h
    have hga : (a.get i (by omega)).toNat = a.digit i.toNat := Mag.get_toNat _ _ _
    have hgb : (b.get i (by omega)).toNat = b.digit i.toNat := Mag.get_toNat _ _ _
    obtain ⟨hs1, hs2⟩ := sub_step (a.get i (by omega)) (b.get i (by omega)) k hk
    simp only [hga, hgb] at hs1
    obtain ⟨k', hk', h1, h2⟩ := ih hs2 (by
      rw [toNat_succ_of_lt h, Mag.valUpTo_set_succ, Mag.valUpTo, Mag.valUpTo,
        show 32 * (i.toNat + 1) = 32 * i.toNat + 32 by omega, Nat.pow_add]
      generalize (2 : Nat) ^ (32 * i.toNat) = X at hinv ⊢
      grind)
    exact ⟨k', hk', h1, by simpa using h2⟩
  | case2 i k c hc hi h =>
    have hle := not_lt_toNat h
    rw [Mag.valUpTo_of_n_le b i.toNat (by omega)] at hinv
    exact subTail_spec a la i hla k c hc _ hk b.val hinv

public theorem Mag.n_subCore (a b : Mag) (hab) : (subCore a b hab).n = a.n := by
  obtain ⟨_, _, _, h2⟩ := subLoop_spec a b a.usize b.usize 0 (Mag.usize_toNat a)
    (Mag.usize_toNat b) hab 0 (Mag.zeros a.usize (by rw [Mag.usize_toNat]; exact a.n_le))
    (by rw [Mag.n_zeros, Mag.usize_toNat]; omega) (by simp) (by simp) (by simp [Mag.valUpTo])
  show (subLoop _ _ _ _ _ _ _ _ _ _ _ _).n = a.n
  simp only [h2, Mag.n_zeros, Mag.usize_toNat]

public theorem val_subCore (a b : Mag) (hab) (hle : b.val ≤ a.val) :
    (subCore a b hab).val = a.val - b.val := by
  obtain ⟨k', hk', h1, -⟩ := subLoop_spec a b a.usize b.usize 0 (Mag.usize_toNat a)
    (Mag.usize_toNat b) hab 0 (Mag.zeros a.usize (by rw [Mag.usize_toNat]; exact a.n_le))
    (by rw [Mag.n_zeros, Mag.usize_toNat]; omega) (by simp) (by simp) (by simp [Mag.valUpTo])
  simp only [Mag.usize_toNat] at h1
  change a.val + k' * _ = b.val + (subCore a b hab).valUpTo a.n at h1
  have hval : (subCore a b hab).val = (subCore a b hab).valUpTo a.n := by
    rw [Mag.val, Mag.n_subCore]
  have := (subCore a b hab).valUpTo_lt a.n
  have := a.val_lt
  -- a borrow out of the top digit would make the result exceed `2^(32 n)`
  rcases (by omega : k' = 0 ∨ k' = 1) with h | h <;> subst h <;> omega

@[simp] public theorem Mag.n_empty : Mag.empty.n = 0 := by
  simp [Mag.empty, Mag.n, Mag.size_replicate]
@[simp] public theorem Mag.val_empty : Mag.empty.val = 0 := by rw [Mag.val, Mag.n_empty]; rfl
public theorem Mag.isNorm_empty : Mag.empty.IsNorm := Or.inl Mag.n_empty

public theorem Mag.n_le_of_val_le (a b : Mag) (hb : b.IsNorm) (hle : b.val ≤ a.val) : b.n ≤ a.n := by
  rcases Nat.eq_zero_or_pos b.n with h | h
  · omega
  · have h1 := b.pow_le_val hb h
    have h2 := a.val_lt
    have : 2 ^ (32 * (b.n - 1)) < 2 ^ (32 * a.n) := by omega
    have := (Nat.pow_lt_pow_iff_right (by omega)).mp this
    omega

/-- `sub` computes truncated subtraction of normalized magnitudes. -/
public theorem val_sub (a b : Mag) (ha : a.IsNorm) (hb : b.IsNorm) :
    (sub a b).val = a.val - b.val ∧ (sub a b).IsNorm := by
  unfold sub
  rw [cmp_spec a b ha hb]
  split
  · next h =>
    have : a.val < b.val := by simpa [Nat.compare_eq_lt] using h
    exact ⟨by rw [Mag.val_empty]; omega, Mag.isNorm_empty⟩
  · next h =>
    have hle : b.val ≤ a.val := by
      have : ¬ compare a.val b.val = .lt := by simpa using h
      rw [Nat.compare_eq_lt] at this; omega
    split
    · exact ⟨by rw [Mag.val_normalize, val_subCore _ _ _ hle], Mag.isNorm_normalize _⟩
    · next hn => exact absurd (Mag.n_le_of_val_le a b hb hle) hn


/-! ## Multiplication -/

public theorem Mag.valUpTo_set (c : Mag) (p : USize) (h) (v : UInt32) (T : Nat) (hp : p.toNat < T) :
    (c.set p h v).valUpTo T + c.digit p.toNat * 2 ^ (32 * p.toNat) =
      c.valUpTo T + v.toNat * 2 ^ (32 * p.toNat) := by
  induction T with
  | zero => omega
  | succ T ih =>
    rw [Mag.valUpTo, Mag.valUpTo, Mag.digit_set]
    by_cases hT : p.toNat < T
    · rw [ite_eq_right (by omega)]; have := ih hT; omega
    · have : p.toNat = T := by omega
      subst this
      rw [ite_eq_left rfl, Mag.valUpTo_set_of_le _ _ _ _ _ (Nat.le_refl _)]
      omega

public theorem Mag.valUpTo_set' (c : Mag) (p : USize) (h) (v : UInt32) (T q : Nat) (hq : p.toNat = q)
    (hp : q < T) :
    (c.set p h v).valUpTo T + c.digit q * 2 ^ (32 * q) = c.valUpTo T + v.toNat * 2 ^ (32 * q) := by
  subst hq; exact c.valUpTo_set p h v T hp

public theorem mul_step (x v d k : Nat) (hx : x < 2 ^ 32) (hv : v < 2 ^ 32) (hd : d < 2 ^ 32)
    (hk : k < 2 ^ 32) : x * v + d + k < 2 ^ 64 := by
  have : x * v ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  have : (2 : Nat) ^ 32 = 4294967296 := rfl
  omega

public theorem mulInner_spec (a : Mag) (la j : USize) (hla) (v : UInt64) (hv : v.toNat < 2 ^ 32) (i : USize)
    (k : UInt64) (c : Mag) (hc) (hi) (hk : k.toNat < 2 ^ 32) (c₀ : Mag) (T : Nat)
    (hT : T = j.toNat + la.toNat + 1)
    (hz : c₀.digit (j.toNat + la.toNat) = 0)
    (hsame : ∀ p, j.toNat + i.toNat ≤ p → c.digit p = c₀.digit p)
    (hinv : c.valUpTo T + k.toNat * 2 ^ (32 * (j.toNat + i.toNat)) =
      c₀.valUpTo T + a.valUpTo i.toNat * v.toNat * 2 ^ (32 * j.toNat)) :
    (mulInner a la j hla v i k c hc hi).valUpTo T =
      c₀.valUpTo T + a.val * v.toNat * 2 ^ (32 * j.toNat) := by
  fun_induction mulInner a la j hla v i k c hc hi with
  | case1 i k c hc hi h hi' hij t ih =>
    have hga : (a.get i (by omega)).toNat = a.digit i.toNat := Mag.get_toNat _ _ _
    have hgc : (c.get (i + j) (by omega)).toNat = c.digit (i.toNat + j.toNat) := by
      rw [Mag.get_toNat, hij]
    have hx := a.digit_lt i.toNat
    have hd := c.digit_lt (i.toNat + j.toNat)
    have hb := mul_step _ _ _ _ hx hv hd hk
    have ht : t.toNat = a.digit i.toNat * v.toNat + c.digit (i.toNat + j.toNat) + k.toNat := by
      simp only [t, UInt64.toNat_add, UInt64.toNat_mul, UInt32.toNat_toUInt64, hga, hgc]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have hcarry : (t >>> 32).toNat = t.toNat / 2 ^ 32 := by
      simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    have hst : t.toUInt32.toNat = t.toNat % 2 ^ 32 := by simp
    have hset := c.valUpTo_set' (i + j) (by omega) t.toUInt32 T _ hij (by omega)
    have hsucc := toNat_succ_of_lt h
    apply ih (by rw [hcarry]; omega)
    · intro p hp
      rw [Mag.digit_set, ite_eq_right (by rw [hij]; omega), hsame p (by omega)]
    · rw [toNat_succ_of_lt h, Mag.valUpTo, hst] at *
      rw [hst] at hset
      rw [hcarry, show 32 * (j.toNat + (i.toNat + 1)) = 32 * (i.toNat + j.toNat) + 32 by omega,
        Nat.pow_add, show 32 * (j.toNat + i.toNat) = 32 * (i.toNat + j.toNat) by omega] at *
      rw [show 32 * (i.toNat + j.toNat) = 32 * i.toNat + 32 * j.toNat by omega, Nat.pow_add] at *
      generalize (2 : Nat) ^ (32 * i.toNat) = X at *
      generalize (2 : Nat) ^ (32 * j.toNat) = Y at *
      have hdm := Nat.div_add_mod t.toNat (2 ^ 32)
      rw [ht] at hdm hset ⊢
      grind
  | case2 i k c hc hi h hjl =>
    have hle := not_lt_toNat h
    have hset := c.valUpTo_set' (j + la) (by omega) k.toUInt32 T _ hjl (by omega)
    have hil : i.toNat = la.toNat := by omega
    rw [hsame (j.toNat + la.toNat) (by omega), hz] at hset
    have hk32 : k.toUInt32.toNat = k.toNat := by simp; omega
    rw [hk32] at hset
    rw [hil, Mag.valUpTo_of_n_le a la.toNat (by omega)] at hinv
    omega


public theorem mulInner_frame (a : Mag) (la j : USize) (hla) (v : UInt64) (i : USize) (k : UInt64) (c : Mag)
    (hc) (hi) (p : Nat) (hp : p < j.toNat + i.toNat ∨ j.toNat + la.toNat < p) :
    (mulInner a la j hla v i k c hc hi).digit p = c.digit p := by
  fun_induction mulInner a la j hla v i k c hc hi with
  | case1 i k c hc hi h hi' hij t ih =>
    have hsucc := toNat_succ_of_lt h
    rw [ih (by omega), Mag.digit_set, ite_eq_right (by rw [hij]; omega)]
  | case2 i k c hc hi h hjl => rw [Mag.digit_set, ite_eq_right (by rw [hjl]; omega)]

public theorem mulOuter_spec (a b : Mag) (la lb j : USize) (hla hlb) (c : Mag) (hc) (hj) (N : Nat)
    (hN : N = la.toNat + lb.toNat)
    (hz : ∀ p, j.toNat + la.toNat ≤ p → c.digit p = 0)
    (hinv : c.valUpTo N = a.val * b.valUpTo j.toNat) :
    (mulOuter a b la lb j hla hlb c hc hj).valUpTo N = a.val * b.val := by
  fun_induction mulOuter a b la lb j hla hlb c hc hj with
  | case1 j c hc hj h hj' v ih =>
    have hsucc := toNat_succ_of_lt h
    have hv : v.toNat = b.digit j.toNat := Mag.get_toNat _ _ _
    apply ih
    · intro p hp
      split
      · exact hz p (by omega)
      · rw [mulInner_frame _ _ _ _ _ _ _ _ _ _ _ (Or.inr (by omega)), hz p (by omega)]
    · rw [hsucc, Mag.valUpTo, ← hv]
      split
      · next h0 =>
        have : v = 0 := by simpa using h0
        rw [this, hinv]; simp
      · next h0 =>
        have hvlt := v.toNat_lt
        have hspec := mulInner_spec a la j hla v.toUInt64 (by simp; omega) 0 0 c (by omega)
          (by simp) (by simp) c (j.toNat + la.toNat + 1) rfl (hz _ (Nat.le_refl _))
          (fun p _ => rfl) (by simp [Mag.valUpTo])
        -- the row leaves the digits beyond `j + la` (all zero) untouched
        have hT : (mulInner a la j hla v.toUInt64 0 0 c (by omega) (by simp)).valUpTo N =
            (mulInner a la j hla v.toUInt64 0 0 c (by omega) (by simp)).valUpTo
              (j.toNat + la.toNat + 1) := by
          apply Mag.valUpTo_eq_of_zero _ _ _ (by omega)
          intro p hp1 hp2
          rw [mulInner_frame _ _ _ _ _ _ _ _ _ _ _ (Or.inr (by omega)), hz p (by omega)]
        have hc0 : c.valUpTo N = c.valUpTo (j.toNat + la.toNat + 1) :=
          Mag.valUpTo_eq_of_zero _ _ _ (by omega) (fun p hp1 _ => hz p (by omega))
        rw [hT, hspec, ← hc0, hinv]
        simp only [UInt32.toNat_toUInt64]
        rw [Nat.mul_add]; grind
  | case2 j c hc hj h =>
    have hle := not_lt_toNat h
    rw [hinv, Mag.valUpTo_of_n_le b j.toNat (by omega)]

@[simp] public theorem n_mulOuter (a b : Mag) (la lb j hla hlb c hc hj) :
    (mulOuter a b la lb j hla hlb c hc hj).n = c.n := by
  fun_induction mulOuter a b la lb j hla hlb c hc hj with
  | case1 j c hc hj h _ v ih => exact ih.trans (by split <;> simp)
  | case2 => rfl

public theorem Mag.valUpTo_zeros (k : USize) (h) (T : Nat) : (Mag.zeros k h).valUpTo T = 0 := by
  induction T with
  | zero => rfl
  | succ T ih => rw [Mag.valUpTo, ih, Mag.digit_zeros]; simp

public theorem val_mulCore (a b : Mag) (h) : (mulCore a b h).val = a.val * b.val := by
  have hn : (mulCore a b h).n = a.n + b.n := by
    show (mulOuter _ _ _ _ _ _ _ _ _ _).n = _
    rw [n_mulOuter, Mag.n_zeros, Mag.usize_add_toNat a b h]
  rw [Mag.val, hn]
  exact mulOuter_spec a b a.usize b.usize 0 (Mag.usize_toNat a) (Mag.usize_toNat b) _ _ (by simp)
    (a.n + b.n) (by rw [Mag.usize_toNat, Mag.usize_toNat]) (fun p _ => Mag.digit_zeros _ _ _)
    (by rw [Mag.valUpTo_zeros]; simp [Mag.valUpTo])

/-- Schoolbook multiplication is correct unless the result exceeds `maxBytes`. -/
public theorem val_mulBasecase (a b : Mag) (h : (a.n + b.n) * 4 ≤ maxBytes) :
    (mulBasecase a b).val = a.val * b.val ∧ (mulBasecase a b).IsNorm := by
  unfold mulBasecase
  rw [dite_eq_left h]
  split
  · exact ⟨by rw [Mag.val_normalize, val_mulCore], Mag.isNorm_normalize _⟩
  · exact ⟨by rw [Mag.val_normalize, val_mulCore, Nat.mul_comm], Mag.isNorm_normalize _⟩


/-! ## Shifts -/

public theorem shl_step (x p s : UInt32) (hs0 : 0 < s.toNat) (hs1 : s.toNat < 32) :
    ((x <<< s) ||| (p >>> (32 - s))).toNat + (x >>> (32 - s)).toNat * 2 ^ 32 =
      x.toNat * 2 ^ s.toNat + (p >>> (32 - s)).toNat := by
  have hsub : (32 - s).toNat = 32 - s.toNat := by
    rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simp; omega))]; simp
  have hp := p.toNat_lt
  have hEF : 2 ^ (32 - s.toNat) * 2 ^ s.toNat = 2 ^ 32 := by
    rw [← Nat.pow_add, show 32 - s.toNat + s.toNat = 32 by omega]
  simp only [UInt32.toNat_or, UInt32.toNat_shiftLeft, UInt32.toNat_shiftRight, hsub,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, show s.toNat % 32 = s.toNat by omega,
    show (32 - s.toNat) % 32 = 32 - s.toNat by omega]
  have hq : p.toNat / 2 ^ (32 - s.toNat) < 2 ^ s.toNat := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), Nat.mul_comm, hEF]; exact hp
  rw [← hEF, Nat.mul_mod_mul_right, ByteArray.or_shift_eq_add _ _ _ hq]
  have hX := Nat.div_add_mod x.toNat (2 ^ (32 - s.toNat))
  generalize 2 ^ (32 - s.toNat) = F at *
  generalize 2 ^ s.toNat = E at *
  generalize p.toNat / F = q at *
  generalize x.toNat = X at *
  rw [← hX]
  grind

public theorem Mag.valUpTo_set_succ' (c : Mag) (p : USize) (h) (v : UInt32) (q : Nat) (hq : p.toNat = q) :
    (c.set p h v).valUpTo (q + 1) = c.valUpTo q + v.toNat * 2 ^ (32 * q) := by
  subst hq; exact c.valUpTo_set_succ p h v

public theorem copyLoop_spec (a : Mag) (la q i : USize) (hla) (c : Mag) (hc) (hi)
    (hz : ∀ p, q.toNat + i.toNat ≤ p → c.digit p = 0)
    (hinv : c.valUpTo (q.toNat + i.toNat) = a.valUpTo i.toNat * 2 ^ (32 * q.toNat)) :
    (copyLoop a la q i hla c hc hi).valUpTo (q.toNat + la.toNat) = a.val * 2 ^ (32 * q.toNat) ∧
      (∀ p, q.toNat + la.toNat ≤ p → (copyLoop a la q i hla c hc hi).digit p = 0) ∧
      (copyLoop a la q i hla c hc hi).n = c.n := by
  fun_induction copyLoop a la q i hla c hc hi with
  | case1 i c hc hi h hi' hqi ih =>
    have hsucc := toNat_succ_of_lt h
    have hg : (a.get i (by omega)).toNat = a.digit i.toNat := Mag.get_toNat _ _ _
    obtain ⟨h1, h2, h3⟩ := ih (fun p hp => by
        rw [Mag.digit_set, ite_eq_right (by rw [hqi]; omega), hz p (by omega)]) (by
      rw [hsucc, show q.toNat + (i.toNat + 1) = (q.toNat + i.toNat) + 1 by omega,
        Mag.valUpTo_set_succ' _ _ _ _ _ hqi, hg, hinv, Mag.valUpTo,
        show 32 * (q.toNat + i.toNat) = 32 * q.toNat + 32 * i.toNat by omega, Nat.pow_add]
      generalize (2 : Nat) ^ (32 * q.toNat) = Y
      generalize (2 : Nat) ^ (32 * i.toNat) = Z
      grind)
    exact ⟨h1, h2, by simp⟩
  | case2 i c hc hi h =>
    have hle := not_lt_toNat h
    have hil : i.toNat = la.toNat := by omega
    rw [hil] at hz hinv
    exact ⟨by rw [hinv, Mag.valUpTo_of_n_le a la.toNat (by omega)], hz, rfl⟩

public theorem shlLoop_spec (a : Mag) (la q : USize) (s : UInt32) (hs0 : 0 < s.toNat) (hs1 : s.toNat < 32)
    (i : USize) (hla) (prev : UInt32) (c : Mag) (hc) (hi)
    (hz : ∀ p, q.toNat + i.toNat ≤ p → c.digit p = 0)
    (hinv : c.valUpTo (q.toNat + i.toNat) + (prev >>> (32 - s)).toNat * 2 ^ (32 * (q.toNat + i.toNat)) =
      a.valUpTo i.toNat * 2 ^ s.toNat * 2 ^ (32 * q.toNat)) :
    (shlLoop a la q s i hla prev c hc hi).valUpTo (q.toNat + la.toNat + 1) =
        a.val * 2 ^ s.toNat * 2 ^ (32 * q.toNat) ∧
      (∀ p, q.toNat + la.toNat + 1 ≤ p → (shlLoop a la q s i hla prev c hc hi).digit p = 0) ∧
      (shlLoop a la q s i hla prev c hc hi).n = c.n := by
  fun_induction shlLoop a la q s i hla prev c hc hi with
  | case1 i prev c hc hi h hi' hqi x ih =>
    have hsucc := toNat_succ_of_lt h
    have hg : x.toNat = a.digit i.toNat := Mag.get_toNat _ _ _
    have hstep := shl_step x prev s hs0 hs1
    obtain ⟨h1, h2, h3⟩ := ih (fun p hp => by
        rw [Mag.digit_set, ite_eq_right (by rw [hqi]; omega), hz p (by omega)]) (by
      rw [hg] at hstep
      rw [hsucc, show q.toNat + (i.toNat + 1) = (q.toNat + i.toNat) + 1 by omega,
        Mag.valUpTo_set_succ' _ _ _ _ _ hqi, Mag.valUpTo,
        show 32 * (q.toNat + i.toNat + 1) = 32 * q.toNat + 32 * i.toNat + 32 by omega,
        show 32 * (q.toNat + i.toNat) = 32 * q.toNat + 32 * i.toNat by omega]
      simp only [Nat.pow_add]
      rw [show 32 * (q.toNat + i.toNat) = 32 * q.toNat + 32 * i.toNat by omega, Nat.pow_add] at hinv
      generalize (2 : Nat) ^ (32 * q.toNat) = Y at hinv ⊢
      generalize (2 : Nat) ^ (32 * i.toNat) = Z at hinv ⊢
      generalize (2 : Nat) ^ s.toNat = E at hinv hstep ⊢
      generalize (x <<< s ||| prev >>> (32 - s)).toNat = d at hstep ⊢
      generalize (x >>> (32 - s)).toNat = c' at hstep ⊢
      generalize (prev >>> (32 - s)).toNat = cr at hstep hinv ⊢
      have h1 := congrArg (· * (Y * Z)) hstep
      simp only [Nat.add_mul] at h1
      grind)
    exact ⟨h1, h2, by simp⟩
  | case2 i prev c hc hi h hql =>
    have hle := not_lt_toNat h
    have hil : i.toNat = la.toNat := by omega
    rw [hil] at hz hinv
    refine ⟨?_, fun p hp => by rw [Mag.digit_set, ite_eq_right (by rw [hql]; omega), hz p (by omega)],
      by simp⟩
    rw [Mag.valUpTo_set_succ' _ _ _ _ _ hql, hinv, Mag.valUpTo_of_n_le a la.toNat (by omega)]

public theorem copyLoop_val (a : Mag) (q : USize) (c : Mag) (hc hi) (hcz : ∀ p, c.digit p = 0)
    (hn : c.n = a.n + q.toNat + 1) :
    (copyLoop a a.usize q 0 (Mag.usize_toNat a) c hc hi).val = a.val * 2 ^ (32 * q.toNat) := by
  obtain ⟨h1, h2, h3⟩ := copyLoop_spec a a.usize q 0 (Mag.usize_toNat a) c hc hi
    (fun p _ => hcz p) (by
      rw [show (0 : USize).toNat = 0 from rfl, Nat.add_zero,
        Mag.valUpTo_eq_of_zero c 0 q.toNat (by omega) (fun p _ _ => hcz p)]; simp [Mag.valUpTo])
  rw [Mag.usize_toNat] at h1 h2
  rw [Mag.val, h3, hn, Mag.valUpTo_eq_of_zero _ (q.toNat + a.n) _ (by omega)
    (fun p hp _ => h2 p hp)]
  exact h1

public theorem shlLoop_val (a : Mag) (q : USize) (s : UInt32) (hs0 : 0 < s.toNat) (hs1 : s.toNat < 32)
    (c : Mag) (hc hi) (hcz : ∀ p, c.digit p = 0) (hn : c.n = a.n + q.toNat + 1) :
    (shlLoop a a.usize q s 0 (Mag.usize_toNat a) 0 c hc hi).val =
      a.val * 2 ^ s.toNat * 2 ^ (32 * q.toNat) := by
  obtain ⟨h1, -, h3⟩ := shlLoop_spec a a.usize q s hs0 hs1 0 (Mag.usize_toNat a) 0 c hc hi
    (fun p _ => hcz p) (by
      rw [show (0 : USize).toNat = 0 from rfl, Nat.add_zero,
        Mag.valUpTo_eq_of_zero c 0 q.toNat (by omega) (fun p _ _ => hcz p)]; simp [Mag.valUpTo])
  rw [Mag.usize_toNat] at h1
  rw [Mag.val, h3, hn, show a.n + q.toNat + 1 = q.toNat + a.n + 1 by omega]
  exact h1

public theorem shiftBuf_toNat (a : Mag) (q : USize) (h : (a.n + q.toNat + 1) * 4 ≤ maxBytes) :
    (a.usize + q + 1).toNat = a.n + q.toNat + 1 := by
  have := maxBytes_lt
  have h1 : (a.usize + q).toNat = a.n + q.toNat := by
    rw [toNat_add_of_lt_size (by rw [Mag.usize_toNat]; omega), Mag.usize_toNat]
  rw [toNat_succ_of_lt_size (by rw [h1]; omega), h1]

public theorem shiftRight5_toNat (sh : USize) : (sh >>> 5).toNat = sh.toNat / 32 := by
  have : (5 : USize).toNat % System.Platform.numBits = 5 := by
    rcases System.Platform.numBits_eq with h | h <;> simp [h]
  rw [USize.toNat_shiftRight, this, Nat.shiftRight_eq_div_pow]

public theorem and31_toNat (sh : USize) : (sh &&& 31).toUInt32.toNat = sh.toNat % 32 := by
  have h1 : (sh &&& 31).toNat = sh.toNat % 32 := by
    rw [USize.toNat_and, show (31 : USize).toNat = 2 ^ 5 - 1 by
      rcases System.Platform.numBits_eq with h | h <;> simp [USize.toNat_ofNat, h],
      Nat.and_two_pow_sub_one_eq_mod]
  simp only [USize.toNat_toUInt32, h1]
  omega

/-- `shiftLeft` multiplies by `2^sh` unless the result exceeds `maxBytes`. -/
public theorem val_shiftLeft (a : Mag) (sh : USize) (h : (a.n + sh.toNat / 32 + 1) * 4 ≤ maxBytes) :
    (shiftLeft a sh).val = a.val * 2 ^ sh.toNat ∧ (shiftLeft a sh).IsNorm := by
  unfold shiftLeft
  dsimp only
  rw [dite_eq_left (by rw [shiftRight5_toNat]; exact h)]
  refine ⟨?_, Mag.isNorm_normalize _⟩
  rw [Mag.val_normalize]
  have hq := shiftRight5_toNat sh
  have hs := and31_toNat sh
  have hsh : 2 ^ sh.toNat = 2 ^ (sh &&& 31).toUInt32.toNat * 2 ^ (32 * (sh >>> 5).toNat) := by
    rw [← Nat.pow_add, hq, hs]; congr 1; omega
  rw [hsh]
  split
  · next h0 =>
    have hs0 : (sh &&& 31).toUInt32.toNat = 0 := by simpa [← UInt32.toNat_inj] using h0
    rw [hs0, Nat.pow_zero, Nat.one_mul]
    apply copyLoop_val _ _ _ _ _ (fun p => Mag.digit_zeros _ _ _)
    rw [Mag.n_zeros, shiftBuf_toNat a _ (by rw [hq]; exact h)]
  · next h0 =>
    have hs0 : 0 < (sh &&& 31).toUInt32.toNat := by
      have : (sh &&& 31).toUInt32.toNat ≠ 0 := fun h' => h0 (by simpa [← UInt32.toNat_inj] using h')
      omega
    rw [← Nat.mul_assoc]
    apply shlLoop_val _ _ _ hs0 (by rw [hs]; omega) _ _ _ (fun p => Mag.digit_zeros _ _ _)
    rw [Mag.n_zeros, shiftBuf_toNat a _ (by rw [hq]; exact h)]


public theorem shr_step (x y s : UInt32) (hs0 : 0 < s.toNat) (hs1 : s.toNat < 32) :
    ((x >>> s) ||| (y <<< (32 - s))).toNat * 2 ^ s.toNat + x.toNat % 2 ^ s.toNat =
      x.toNat + y.toNat % 2 ^ s.toNat * 2 ^ 32 := by
  have hsub : (32 - s).toNat = 32 - s.toNat := by
    rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simp; omega))]; simp
  have hx := x.toNat_lt
  have hEF : 2 ^ s.toNat * 2 ^ (32 - s.toNat) = 2 ^ 32 := by
    rw [← Nat.pow_add, show s.toNat + (32 - s.toNat) = 32 by omega]
  simp only [UInt32.toNat_or, UInt32.toNat_shiftLeft, UInt32.toNat_shiftRight, hsub,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, show s.toNat % 32 = s.toNat by omega,
    show (32 - s.toNat) % 32 = 32 - s.toNat by omega]
  have hq : x.toNat / 2 ^ s.toNat < 2 ^ (32 - s.toNat) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), Nat.mul_comm, hEF]; exact hx
  rw [← hEF, Nat.mul_mod_mul_right, Nat.or_comm, ByteArray.or_shift_eq_add _ _ _ hq]
  have hX := Nat.div_add_mod x.toNat (2 ^ s.toNat)
  generalize 2 ^ (32 - s.toNat) = F at *
  generalize 2 ^ s.toNat = E at *
  generalize x.toNat / E = q at *
  generalize y.toNat % E = r at *
  generalize x.toNat = X at *
  rw [← hX]
  grind

/-- The value of the `i` digits starting at digit `q`. -/
@[expose] public def Mag.valFrom (a : Mag) (q : Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => a.valFrom q i + a.digit (q + i) * 2 ^ (32 * i)

public theorem Mag.valUpTo_add (a : Mag) (q i : Nat) :
    a.valUpTo (q + i) = a.valUpTo q + 2 ^ (32 * q) * a.valFrom q i := by
  induction i with
  | zero => simp [Mag.valFrom]
  | succ i ih =>
    rw [show q + (i + 1) = (q + i) + 1 by omega, Mag.valUpTo, ih, Mag.valFrom,
      show 32 * (q + i) = 32 * q + 32 * i by omega, Nat.pow_add]
    generalize (2 : Nat) ^ (32 * q) = Y; generalize (2 : Nat) ^ (32 * i) = Z
    grind

public theorem copyDown_spec (a : Mag) (q n : USize) (hqn) (i : USize) (c : Mag) (hc) (hi)
    (hinv : c.valUpTo i.toNat = a.valFrom q.toNat i.toNat) :
    (copyDown a q n hqn i c hc hi).valUpTo n.toNat = a.valFrom q.toNat n.toNat ∧
      (copyDown a q n hqn i c hc hi).n = c.n := by
  fun_induction copyDown a q n hqn i c hc hi with
  | case1 i c hc hi h hi' hqi ih =>
    have hsucc := toNat_succ_of_lt h
    have hg : (a.get (q + i) (by omega)).toNat = a.digit (q.toNat + i.toNat) := by
      rw [Mag.get_toNat, hqi]
    obtain ⟨h1, h2⟩ := ih (by
      rw [hsucc, Mag.valUpTo_set_succ, hinv, Mag.valFrom, hg])
    exact ⟨h1, by simpa using h2⟩
  | case2 i c hc hi h =>
    have hle := not_lt_toNat h
    rw [show i.toNat = n.toNat by omega] at hinv
    exact ⟨hinv, rfl⟩

public theorem shrLoop_spec (a : Mag) (q n : USize) (s : UInt32) (hs0 : 0 < s.toNat) (hs1 : s.toNat < 32)
    (hqn) (i : USize) (c : Mag) (hc) (hi)
    (hinv : c.valUpTo i.toNat * 2 ^ s.toNat + a.digit q.toNat % 2 ^ s.toNat =
      a.valFrom q.toNat i.toNat + a.digit (q.toNat + i.toNat) % 2 ^ s.toNat * 2 ^ (32 * i.toNat)) :
    (shrLoop a q n s hqn i c hc hi).valUpTo n.toNat * 2 ^ s.toNat + a.digit q.toNat % 2 ^ s.toNat =
        a.valFrom q.toNat n.toNat ∧
      (shrLoop a q n s hqn i c hc hi).n = c.n := by
  fun_induction shrLoop a q n s hqn i c hc hi with
  | case1 i c hc hi h hi' hqi x y ih =>
    have hsucc := toNat_succ_of_lt h
    have hx : x.toNat = a.digit (q.toNat + i.toNat) := by
      simp only [x]; rw [Mag.get_toNat, hqi]
    have hy : y.toNat = a.digit (q.toNat + i.toNat + 1) := by
      simp only [y]; split
      · next h2 =>
        rw [Mag.get_toNat]
        congr 1
        rw [toNat_succ_of_lt_size (by have := a.n_lt_size; omega), hqi]
      · next h2 =>
        have : n.toNat ≤ i.toNat + 1 := by
          have := not_lt_toNat h2; rw [toNat_succ_of_lt h] at this; omega
        rw [Mag.digit_of_n_le _ _ (by omega)]; rfl
    have hstep := shr_step x y s hs0 hs1
    rw [hx, hy] at hstep
    obtain ⟨h1, h2⟩ := ih (by
      rw [hsucc, Mag.valUpTo_set_succ, Mag.valFrom, show q.toNat + (i.toNat + 1) = q.toNat + i.toNat + 1
        by omega, show 32 * (i.toNat + 1) = 32 * i.toNat + 32 by omega, Nat.pow_add]
      generalize (2 : Nat) ^ (32 * i.toNat) = Z at hinv ⊢
      generalize (2 : Nat) ^ s.toNat = E at hinv hstep ⊢
      generalize ((x >>> s) ||| (y <<< (32 - s))).toNat = d at hstep ⊢
      have h1 := congrArg (· * Z) hstep
      simp only [Nat.add_mul] at h1
      grind)
    exact ⟨h1, by simp⟩
  | case2 i c hc hi h =>
    have hle := not_lt_toNat h
    rw [show i.toNat = n.toNat by omega, Mag.digit_of_n_le a (q.toNat + n.toNat) (by omega)] at hinv
    exact ⟨by rw [hinv]; simp, rfl⟩


public theorem copyDown_val (a : Mag) (q n : USize) (hqn) (c : Mag) (hc hi) (hn : c.n = n.toNat) :
    (copyDown a q n hqn 0 c hc hi).val = a.valFrom q.toNat n.toNat := by
  obtain ⟨h1, h2⟩ := copyDown_spec a q n hqn 0 c hc hi (by
    show c.valUpTo 0 = a.valFrom q.toNat 0; rfl)
  rw [Mag.val, h2, hn]; exact h1

public theorem shrLoop_val (a : Mag) (q n : USize) (s : UInt32) (hs0 : 0 < s.toNat) (hs1 : s.toNat < 32)
    (hqn) (c : Mag) (hc hi) (hn : c.n = n.toNat) :
    (shrLoop a q n s hqn 0 c hc hi).val * 2 ^ s.toNat + a.digit q.toNat % 2 ^ s.toNat =
      a.valFrom q.toNat n.toNat := by
  obtain ⟨h1, h2⟩ := shrLoop_spec a q n s hs0 hs1 hqn 0 c hc hi (by
    show c.valUpTo 0 * _ + _ = a.valFrom q.toNat 0 + a.digit (q.toNat + 0) % _ * 2 ^ (32 * 0)
    simp [Mag.valUpTo, Mag.valFrom])
  rw [Mag.val, h2, hn]; exact h1

public theorem Mag.val_split (a : Mag) (q n : Nat) (hqn : q + n = a.n) :
    a.val = a.valUpTo q + 2 ^ (32 * q) * a.valFrom q n := by
  rw [Mag.val, ← hqn, Mag.valUpTo_add]

public theorem div_pow_split (lo hi Y : Nat) (hlo : lo < Y) : (lo + Y * hi) / Y = hi := by
  rw [Nat.add_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hlo, Nat.add_zero]

public theorem shrLoop_val' (a : Mag) (q n : USize) (s : UInt32) (hs0 : 0 < s.toNat) (hs1 : s.toNat < 32)
    (hqn) (c : Mag) (hc hi) (hn : c.n = n.toNat) :
    (shrLoop a q n s hqn 0 c hc hi).val = a.valFrom q.toNat n.toNat / 2 ^ s.toNat := by
  rw [← shrLoop_val a q n s hs0 hs1 hqn c hc hi hn, Nat.add_comm, Nat.mul_comm,
    div_pow_split _ _ _ (Nat.mod_lt _ (Nat.two_pow_pos _))]

/-- `shiftRight` divides by `2^sh`. -/
public theorem val_shiftRight (a : Mag) (sh : USize) :
    (shiftRight a sh).val = a.val / 2 ^ sh.toNat ∧ (shiftRight a sh).IsNorm := by
  have hq := shiftRight5_toNat sh
  have hs := and31_toNat sh
  have hsh : 2 ^ sh.toNat = 2 ^ (32 * (sh >>> 5).toNat) * 2 ^ (sh &&& 31).toUInt32.toNat := by
    rw [← Nat.pow_add, hq, hs]; congr 1; omega
  unfold shiftRight
  dsimp only
  split
  · next h =>
    refine ⟨?_, Mag.isNorm_normalize _⟩
    rw [Mag.val_normalize, hsh, ← Nat.div_div_eq_div_mul]
    have hn : (a.usize - sh >>> 5).toNat = a.n - (sh >>> 5).toNat := by
      rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr (by rw [Mag.usize_toNat]; omega)),
        Mag.usize_toNat]
    have hsplit := a.val_split (sh >>> 5).toNat (a.usize - sh >>> 5).toNat (by rw [hn]; omega)
    have hlo := a.valUpTo_lt (sh >>> 5).toNat
    rw [hsplit, show 32 * (sh >>> 5).toNat = 32 * (sh >>> 5).toNat from rfl,
      div_pow_split _ _ _ hlo]
    split
    · next h0 =>
      have hs0 : (sh &&& 31).toUInt32.toNat = 0 := by simpa [← UInt32.toNat_inj] using h0
      rw [hs0, Nat.pow_zero, Nat.div_one]
      exact copyDown_val _ _ _ _ _ _ _ (by rw [Mag.n_zeros])
    · next h0 =>
      have hs0 : 0 < (sh &&& 31).toUInt32.toNat := by
        have : (sh &&& 31).toUInt32.toNat ≠ 0 := fun h' => h0 (by simpa [← UInt32.toNat_inj] using h')
        omega
      exact shrLoop_val' a _ _ _ hs0 (by rw [hs]; omega) _ _ _ _ (by rw [Mag.n_zeros])
  · next h =>
    refine ⟨?_, Mag.isNorm_empty⟩
    rw [Mag.val_empty, eq_comm, Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)]
    have := a.val_lt
    have : 2 ^ (32 * a.n) ≤ 2 ^ sh.toNat :=
      Nat.pow_le_pow_right (by omega) (by omega)
    omega


/-! ## Bitwise operations -/

public theorem Mag.val_div_mod (a : Mag) (q : Nat) : a.val / 2 ^ (32 * q) % 2 ^ 32 = a.digit q := by
  have hM := a.valUpTo_of_n_le (max a.n (q + 1)) (by omega)
  have hs := a.valUpTo_add (q + 1) (max a.n (q + 1) - (q + 1))
  rw [show q + 1 + (max a.n (q + 1) - (q + 1)) = max a.n (q + 1) by omega, hM, Mag.valUpTo] at hs
  rw [hs, show 32 * (q + 1) = 32 * q + 32 by omega, Nat.pow_add]
  have hlo := a.valUpTo_lt q
  have hd := a.digit_lt q
  generalize a.valFrom (q + 1) (max a.n (q + 1) - (q + 1)) = R
  generalize a.valUpTo q = lo at *
  generalize a.digit q = d at *
  generalize (2 : Nat) ^ (32 * q) = Y at *
  rw [show lo + d * Y + Y * 2 ^ 32 * R = lo + Y * (d + 2 ^ 32 * R) by
      grind,
    div_pow_split _ _ _ hlo, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd]

/-- Bit `j` of a value is bit `j % 32` of its digit `j / 32`. -/
public theorem Mag.testBit_val (a : Mag) (j : Nat) :
    a.val.testBit j = (a.digit (j / 32)).testBit (j % 32) := by
  rw [← a.val_div_mod (j / 32), Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow,
    show j % 32 + 32 * (j / 32) = j by omega]
  simp [Nat.mod_lt j (show 32 > 0 by omega)]

public theorem getOr0_toNat (a : Mag) (i : USize) : (getOr0 a i).toNat = a.digit i.toNat := by
  unfold getOr0
  split
  · exact Mag.get_toNat _ _ _
  · next h =>
    have := not_lt_toNat h
    rw [Mag.usize_toNat] at this
    rw [Mag.digit_of_n_le _ _ this]; rfl

public theorem zipLoop_n (f : UInt32 → UInt32 → UInt32) (a b : Mag) (n i : USize) (c : Mag) (hc hi) :
    (zipLoop f a b n i c hc hi).n = c.n := by
  fun_induction zipLoop f a b n i c hc hi with
  | case1 i c hc hi h hi' ih => simpa using ih
  | case2 => rfl

public theorem zipLoop_digit (f : UInt32 → UInt32 → UInt32) (g : Nat → Nat → Nat)
    (hf : ∀ x y : UInt32, (f x y).toNat = g x.toNat y.toNat)
    (a b : Mag) (n i : USize) (c : Mag) (hc hi) (p : Nat) :
    (zipLoop f a b n i c hc hi).digit p =
      if i.toNat ≤ p ∧ p < n.toNat then g (a.digit p) (b.digit p) else c.digit p := by
  fun_induction zipLoop f a b n i c hc hi with
  | case1 i c hc hi h hi' ih =>
    have hsucc := toNat_succ_of_lt h
    rw [ih, Mag.digit_set, hsucc]
    by_cases hp : p = i.toNat
    · subst hp
      rw [ite_eq_right (by omega), ite_eq_left rfl, ite_eq_left (by omega), hf, getOr0_toNat, getOr0_toNat]
    · rw [ite_eq_right hp]
      by_cases hq : i.toNat + 1 ≤ p ∧ p < n.toNat
      · rw [ite_eq_left hq, ite_eq_left (by omega)]
      · rw [ite_eq_right hq, ite_eq_right (by omega)]
  | case2 i c hc hi h =>
    have := not_lt_toNat h
    rw [ite_eq_right (by omega)]

public theorem zipWith_n (f : UInt32 → UInt32 → UInt32) (a b : Mag) (n : USize) (hn) :
    (zipWith f a b n hn).n = n.toNat := by
  unfold zipWith; rw [zipLoop_n, Mag.n_zeros]

public theorem zipWith_digit (f : UInt32 → UInt32 → UInt32) (g : Nat → Nat → Nat)
    (hf : ∀ x y : UInt32, (f x y).toNat = g x.toNat y.toNat) (a b : Mag) (n : USize) (hn) (p : Nat) :
    (zipWith f a b n hn).digit p = if p < n.toNat then g (a.digit p) (b.digit p) else 0 := by
  unfold zipWith
  rw [zipLoop_digit f g hf, Mag.digit_zeros]
  simp

public theorem ite_usize_min (a b : Mag) :
    (if a.usize ≤ b.usize then a.usize else b.usize).toNat = min a.n b.n := by
  have ha := a.usize_toNat; have hb := b.usize_toNat
  split
  · next h => have := USize.le_iff_toNat_le.mp h; omega
  · next h =>
    have : ¬ a.usize.toNat ≤ b.usize.toNat := fun h' => h (USize.le_iff_toNat_le.mpr h')
    omega

public theorem ite_usize_max (a b : Mag) :
    (if a.usize ≤ b.usize then b.usize else a.usize).toNat = max a.n b.n := by
  have ha := a.usize_toNat; have hb := b.usize_toNat
  split
  · next h => have := USize.le_iff_toNat_le.mp h; omega
  · next h =>
    have : ¬ a.usize.toNat ≤ b.usize.toNat := fun h' => h (USize.le_iff_toNat_le.mpr h')
    omega

public theorem val_land (a b : Mag) : (land a b).val = a.val &&& b.val ∧ (land a b).IsNorm := by
  refine ⟨?_, Mag.isNorm_normalize _⟩
  unfold land
  rw [Mag.val_normalize]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Mag.testBit_val, zipWith_digit _ (· &&& ·) (fun x y => UInt32.toNat_and x y), ite_usize_min,
    Nat.testBit_and, Mag.testBit_val, Mag.testBit_val]
  split
  · rw [Nat.testBit_and]
  · next hp =>
    rcases (show a.n ≤ j / 32 ∨ b.n ≤ j / 32 by omega) with h | h <;>
      simp [Mag.digit_of_n_le _ _ h]

public theorem val_xor (a b : Mag) : (xor a b).val = a.val ^^^ b.val ∧ (xor a b).IsNorm := by
  refine ⟨?_, Mag.isNorm_normalize _⟩
  unfold xor
  rw [Mag.val_normalize]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Mag.testBit_val, zipWith_digit _ (· ^^^ ·) (fun x y => UInt32.toNat_xor x y), ite_usize_max,
    Nat.testBit_xor, Mag.testBit_val, Mag.testBit_val]
  split
  · rw [Nat.testBit_xor]
  · next hp =>
    simp [Mag.digit_of_n_le a (j / 32) (by omega), Mag.digit_of_n_le b (j / 32) (by omega)]

public theorem val_lor (a b : Mag) (ha : a.IsNorm) (hb : b.IsNorm) :
    (lor a b).val = a.val ||| b.val ∧ (lor a b).IsNorm := by
  have hdig := zipWith_digit _ (· ||| ·) (fun x y => UInt32.toNat_or x y) a b
    (if a.usize ≤ b.usize then b.usize else a.usize) (by rw [ite_usize_max]; exact Nat.le_refl _)
  have hn := zipWith_n (· ||| ·) a b (if a.usize ≤ b.usize then b.usize else a.usize)
    (by rw [ite_usize_max]; exact Nat.le_refl _)
  replace hn := hn.trans (ite_usize_max a b)
  unfold lor
  refine ⟨?_, ?_⟩
  · apply Nat.eq_of_testBit_eq
    intro j
    rw [Mag.testBit_val, hdig, ite_usize_max, Nat.testBit_or, Mag.testBit_val, Mag.testBit_val]
    split
    · rw [Nat.testBit_or]
    · next hp =>
      simp [Mag.digit_of_n_le a (j / 32) (by omega), Mag.digit_of_n_le b (j / 32) (by omega)]
  · unfold Mag.IsNorm
    rw [hn, hdig, ite_usize_max]
    rcases Nat.eq_zero_or_pos (max a.n b.n) with h0 | h0
    · exact Or.inl h0
    · refine Or.inr fun h => ?_
      rw [ite_eq_left (by omega), Nat.or_eq_zero_iff] at h
      rcases Nat.le_total b.n a.n with hle | hle
      · rcases ha with ha | ha
        · omega
        · exact ha (by rw [show a.n - 1 = max a.n b.n - 1 by omega]; exact h.1)
      · rcases hb with hb | hb
        · omega
        · exact hb (by rw [show b.n - 1 = max a.n b.n - 1 by omega]; exact h.2)


/-! ## Single-digit operations -/

public theorem mulAddSmallLoop_spec (a : Mag) (la : USize) (hla) (m : UInt64) (hm : m.toNat < 2 ^ 32)
    (i : USize) (k : UInt64) (c : Mag) (hc hi) (hk : k.toNat < 2 ^ 32) (k₀ : Nat)
    (hinv : c.valUpTo i.toNat + k.toNat * 2 ^ (32 * i.toNat) = a.valUpTo i.toNat * m.toNat + k₀) :
    (mulAddSmallLoop a la hla m i k c hc hi).valUpTo (la.toNat + 1) = a.val * m.toNat + k₀ ∧
      (mulAddSmallLoop a la hla m i k c hc hi).n = c.n := by
  fun_induction mulAddSmallLoop a la hla m i k c hc hi with
  | case1 i k c hc hi h hi' t ih =>
    have hga : (a.get i (by omega)).toNat = a.digit i.toNat := Mag.get_toNat _ _ _
    have hx := a.digit_lt i.toNat
    have hb := mul_step _ _ 0 _ hx hm (by omega) hk
    have ht : t.toNat = a.digit i.toNat * m.toNat + k.toNat := by
      simp only [t, UInt64.toNat_add, UInt64.toNat_mul, UInt32.toNat_toUInt64, hga]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have hcarry : (t >>> 32).toNat = t.toNat / 2 ^ 32 := by
      simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    have hst : t.toUInt32.toNat = t.toNat % 2 ^ 32 := by simp
    obtain ⟨h1, h2⟩ := ih (by rw [hcarry]; omega) (by
      rw [toNat_succ_of_lt h, Mag.valUpTo_set_succ, hst, hcarry, Mag.valUpTo,
        show 32 * (i.toNat + 1) = 32 * i.toNat + 32 by omega, Nat.pow_add]
      have hdm := Nat.div_add_mod t.toNat (2 ^ 32)
      rw [ht] at hdm ⊢
      generalize (2 : Nat) ^ (32 * i.toNat) = X at *
      grind)
    exact ⟨h1, by simpa using h2⟩
  | case2 i k c hc hi h =>
    have hle := not_lt_toNat h
    have hil : i.toNat = la.toNat := by omega
    have hk32 : k.toUInt32.toNat = k.toNat := by simp; omega
    refine ⟨?_, by simp⟩
    rw [Mag.valUpTo_set_succ, hk32, ← hil, hinv, hil, Mag.valUpTo_of_n_le a la.toNat (by omega)]

/-- `mulAddSmall` computes `a * m + k` unless the result exceeds `maxBytes`. -/
public theorem val_mulAddSmall (a : Mag) (m k : UInt32) (h : (a.n + 1) * 4 ≤ maxBytes) :
    (mulAddSmall a m k).val = a.val * m.toNat + k.toNat ∧ (mulAddSmall a m k).IsNorm := by
  unfold mulAddSmall
  rw [dite_eq_left h]
  refine ⟨?_, Mag.isNorm_normalize _⟩
  rw [Mag.val_normalize]
  obtain ⟨h1, h2⟩ := mulAddSmallLoop_spec a a.usize a.usize_toNat m.toUInt64
    (by simpa using m.toNat_lt) 0 k.toUInt64 _ _ _ (by simpa using k.toNat_lt) k.toNat
    (by simp [Mag.valUpTo])
  rw [Mag.val, h2, Mag.n_zeros, a.usize_succ_toNat, ← a.usize_toNat]
  simpa using h1

public theorem div1_word (r : UInt64) (x : UInt32) (hr : r.toNat < 2 ^ 32) :
    ((r <<< 32) ||| x.toUInt64).toNat = r.toNat * 2 ^ 32 + x.toNat := by
  have hx := x.toNat_lt
  rw [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt32.toNat_toUInt64,
    show (32 : UInt64).toNat % 64 = 32 from rfl, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (by
      have : r.toNat * 2 ^ 32 < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul_of_pos_right hr (by decide)
      exact Nat.lt_of_lt_of_le this (by decide)),
    ByteArray.or_shift_eq_add _ _ _ (by simpa using hx)]

public theorem Mag.val_set_of_zero (c : Mag) (p : USize) (h) (v : UInt32) (hz : c.digit p.toNat = 0) :
    (c.set p h v).val = c.val + v.toNat * 2 ^ (32 * p.toNat) := by
  have := c.valUpTo_set p h v c.n h
  rw [hz] at this
  rw [Mag.val, Mag.val, show (c.set p h v).n = c.n by simp]
  omega

public theorem div1Loop_spec (a : Mag) (d : UInt64) (hd0 : 0 < d.toNat) (hd : d.toNat ≤ 2 ^ 32)
    (j : USize) (hj) (r : UInt64) (q : Mag) (hq) (hr : r.toNat < d.toNat)
    (hz : ∀ p, p < j.toNat → q.digit p = 0)
    (hinv : a.val = a.valUpTo j.toNat + q.val * d.toNat + r.toNat * 2 ^ (32 * j.toNat)) :
    a.val = (div1Loop a d j hj r q hq).1.val * d.toNat + (div1Loop a d j hj r q hq).2.toNat ∧
      (div1Loop a d j hj r q hq).2.toNat < d.toNat := by
  fun_induction div1Loop a d j hj r q hq with
  | case1 j hj r q hq h hj0 hp t ih =>
    have hga : (a.get (j - 1) (by omega)).toNat = a.digit (j.toNat - 1) := by
      rw [Mag.get_toNat, hp]
    have ht : t.toNat = r.toNat * 2 ^ 32 + a.digit (j.toNat - 1) := by
      simp only [t]; rw [div1_word _ _ (by omega), hga]
    have hx := a.digit_lt (j.toNat - 1)
    have htd : t.toNat < d.toNat * 2 ^ 32 := by
      rw [ht]
      have : r.toNat * 2 ^ 32 + 2 ^ 32 ≤ d.toNat * 2 ^ 32 := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hr
      omega
    have hqd : (t / d).toUInt32.toNat = t.toNat / d.toNat := by
      simp only [UInt64.toNat_toUInt32, UInt64.toNat_div]
      exact Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul htd)
    have hmd : (t % d).toNat = t.toNat % d.toNat := UInt64.toNat_mod _ _
    apply ih (by rw [hmd]; exact Nat.mod_lt _ hd0)
    · intro p hpj
      rw [Mag.digit_set, ite_eq_right (by rw [hp]; omega), hz p (by omega)]
    · rw [Mag.val_set_of_zero _ _ _ _ (by rw [hp]; exact hz _ (by omega)), hqd, hmd, hp]
      have hv : a.valUpTo j.toNat = a.valUpTo (j.toNat - 1) + a.digit (j.toNat - 1) * 2 ^ (32 * (j.toNat - 1)) := by
        conv => lhs; rw [show j.toNat = (j.toNat - 1) + 1 by omega]
        rfl
      rw [hv, show 32 * j.toNat = 32 * (j.toNat - 1) + 32 by omega, Nat.pow_add] at hinv
      have hdm := Nat.div_add_mod t.toNat d.toNat
      rw [ht] at hdm ⊢
      generalize (2 : Nat) ^ (32 * (j.toNat - 1)) = X at *
      generalize (r.toNat * 2 ^ 32 + a.digit (j.toNat - 1)) / d.toNat = Q at *
      generalize (r.toNat * 2 ^ 32 + a.digit (j.toNat - 1)) % d.toNat = R at *
      grind
  | case2 j hj r q hq h =>
    have : j.toNat = 0 := by
      have := not_lt_toNat h; simp at this; omega
    rw [this] at hinv
    refine ⟨?_, hr⟩
    simpa [Mag.valUpTo] using hinv

/-- `divModSmall` computes quotient and remainder by a nonzero digit. -/
public theorem val_divModSmall (a : Mag) (d : UInt32) (hd : 0 < d.toNat) :
    (divModSmall a d).1.val = a.val / d.toNat ∧ (divModSmall a d).2.toNat = a.val % d.toNat ∧
      (divModSmall a d).1.IsNorm := by
  have hdl := d.toNat_lt
  obtain ⟨h1, h2⟩ := div1Loop_spec a d.toUInt64 (by simpa using hd) (by simp; omega) a.usize
    a.usize_le 0 (Mag.zeros a.usize (by rw [a.usize_toNat]; exact a.n_le)) _ (by simpa using hd)
    (fun p _ => Mag.digit_zeros _ _ _)
    (by rw [Mag.valUpTo_of_n_le a a.usize.toNat (by rw [a.usize_toNat]; exact Nat.le_refl _),
          Mag.val, Mag.val, Mag.valUpTo_zeros]
        simp)
  simp only [UInt32.toNat_toUInt64] at h1 h2
  unfold divModSmall
  dsimp only
  refine ⟨?_, ?_, Mag.isNorm_normalize _⟩
  · rw [Mag.val_normalize, h1, Nat.add_comm, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt h2,
      Nat.zero_add]
  · rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt (by omega), h1, Nat.add_comm,
      Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt h2]

end Nat.Big
