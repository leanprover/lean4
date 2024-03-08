/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix
-/
prelude
import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas

namespace BitVec

/--
This normalized a bitvec using `ofFin` to `ofNat`.
-/
theorem ofFin_eq_ofNat : @BitVec.ofFin w (Fin.mk x lt) = BitVec.ofNat w x := by
  simp only [BitVec.ofNat, Fin.ofNat', lt, Nat.mod_eq_of_lt]

/-- Prove equality of bitvectors in terms of nat operations. -/
theorem eq_of_toNat_eq {n} : ∀ {i j : BitVec n}, i.toNat = j.toNat → i = j
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

@[simp] theorem val_toFin (x : BitVec w) : x.toFin.val = x.toNat := rfl

@[bv_toNat] theorem toNat_eq (x y : BitVec n) : x = y ↔ x.toNat = y.toNat :=
  Iff.intro (congrArg BitVec.toNat) eq_of_toNat_eq

@[bv_toNat] theorem toNat_ne (x y : BitVec n) : x ≠ y ↔ x.toNat ≠ y.toNat := by
  rw [Ne, toNat_eq]

theorem testBit_toNat (x : BitVec w) : x.toNat.testBit i = x.getLsb i := rfl

@[simp] theorem getLsb_ofFin (x : Fin (2^n)) (i : Nat) :
  getLsb (BitVec.ofFin x) i = x.val.testBit i := rfl

@[simp] theorem getLsb_ge (x : BitVec w) (i : Nat) (ge : w ≤ i) : getLsb x i = false := by
  let ⟨x, x_lt⟩ := x
  simp
  apply Nat.testBit_lt_two_pow
  have p : 2^w ≤ 2^i := Nat.pow_le_pow_of_le_right (by omega) ge
  omega

theorem lt_of_getLsb (x : BitVec w) (i : Nat) : getLsb x i = true → i < w := by
  if h : i < w then
    simp [h]
  else
    simp [Nat.ge_of_not_lt h]

-- We choose `eq_of_getLsb_eq` as the `@[ext]` theorem for `BitVec`
-- somewhat arbitrarily over `eq_of_getMsg_eq`.
@[ext] theorem eq_of_getLsb_eq {x y : BitVec w}
    (pred : ∀(i : Fin w), x.getLsb i.val = y.getLsb i.val) : x = y := by
  apply eq_of_toNat_eq
  apply Nat.eq_of_testBit_eq
  intro i
  if i_lt : i < w then
    exact pred ⟨i, i_lt⟩
  else
    have p : i ≥ w := Nat.le_of_not_gt i_lt
    simp [testBit_toNat, getLsb_ge _ _ p]

theorem eq_of_getMsb_eq {x y : BitVec w}
    (pred : ∀(i : Fin w), x.getMsb i = y.getMsb i.val) : x = y := by
  simp only [getMsb] at pred
  apply eq_of_getLsb_eq
  intro ⟨i, i_lt⟩
  if w_zero : w = 0 then
    simp [w_zero]
  else
    have w_pos := Nat.pos_of_ne_zero w_zero
    have r : i ≤ w - 1 := by
      simp [Nat.le_sub_iff_add_le w_pos, Nat.add_succ]
      exact i_lt
    have q_lt : w - 1 - i < w := by
      simp only [Nat.sub_sub]
      apply Nat.sub_lt w_pos
      simp [Nat.succ_add]
    have q := pred ⟨w - 1 - i, q_lt⟩
    simpa [q_lt, Nat.sub_sub_self, r] using q

@[simp] theorem of_length_zero {x : BitVec 0} : x = 0#0 := by ext; simp

theorem eq_of_toFin_eq : ∀ {x y : BitVec w}, x.toFin = y.toFin → x = y
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

@[simp] theorem toNat_ofBool (b : Bool) : (ofBool b).toNat = b.toNat := by
  cases b <;> rfl

@[simp] theorem msb_ofBool (b : Bool) : (ofBool b).msb = b := by
  cases b <;> simp [BitVec.msb]

theorem ofNat_one (n : Nat) : BitVec.ofNat 1 n = BitVec.ofBool (n % 2 = 1) :=  by
  rcases (Nat.mod_two_eq_zero_or_one n) with h | h <;> simp [h, BitVec.ofNat, Fin.ofNat']

theorem ofBool_eq_iff_eq : ∀(b b' : Bool), BitVec.ofBool b = BitVec.ofBool b' ↔ b = b' := by
  decide

@[simp, bv_toNat] theorem toNat_ofFin (x : Fin (2^n)) : (BitVec.ofFin x).toNat = x.val := rfl

@[simp] theorem toNat_ofNatLt (x : Nat) (p : x < 2^w) : (x#'p).toNat = x := rfl

@[simp] theorem getLsb_ofNatLt {n : Nat} (x : Nat) (lt : x < 2^n) (i : Nat) :
  getLsb (x#'lt) i = x.testBit i := by
  simp [getLsb, BitVec.ofNatLt]

@[simp, bv_toNat] theorem toNat_ofNat (x w : Nat) : (x#w).toNat = x % 2^w := by
  simp [BitVec.toNat, BitVec.ofNat, Fin.ofNat']

-- Remark: we don't use `[simp]` here because simproc` subsumes it for literals.
-- If `x` and `n` are not literals, applying this theorem eagerly may not be a good idea.
theorem getLsb_ofNat (n : Nat) (x : Nat) (i : Nat) :
  getLsb (x#n) i = (i < n && x.testBit i) := by
  simp [getLsb, BitVec.ofNat, Fin.val_ofNat']

@[simp, deprecated toNat_ofNat] theorem toNat_zero (n : Nat) : (0#n).toNat = 0 := by trivial

@[simp] theorem getLsb_zero : (0#w).getLsb i = false := by simp [getLsb]

@[simp] theorem getMsb_zero : (0#w).getMsb i = false := by simp [getMsb]

@[simp] theorem toNat_mod_cancel (x : BitVec n) : x.toNat % (2^n) = x.toNat :=
  Nat.mod_eq_of_lt x.isLt

private theorem lt_two_pow_of_le {x m n : Nat} (lt : x < 2 ^ m) (le : m ≤ n) : x < 2 ^ n :=
  Nat.lt_of_lt_of_le lt (Nat.pow_le_pow_of_le_right (by trivial : 0 < 2) le)

/-! ### msb -/

@[simp] theorem msb_zero : (0#w).msb = false := by simp [BitVec.msb, getMsb]

theorem msb_eq_getLsb_last (x : BitVec w) :
    x.msb = x.getLsb (w - 1) := by
  simp [BitVec.msb, getMsb, getLsb]
  rcases w  with rfl | w
  · simp [BitVec.eq_nil x]
  · simp

@[bv_toNat] theorem getLsb_last (x : BitVec w) :
    x.getLsb (w-1) = decide (2 ^ (w-1) ≤ x.toNat) := by
  rcases w with rfl | w
  · simp
  · simp only [Nat.zero_lt_succ, decide_True, getLsb, Nat.testBit, Nat.succ_sub_succ_eq_sub,
    Nat.sub_zero, Nat.and_one_is_mod, Bool.true_and, Nat.shiftRight_eq_div_pow]
    rcases (Nat.lt_or_ge (BitVec.toNat x) (2 ^ w)) with h | h
    · simp [Nat.div_eq_of_lt h, h]
    · simp only [h]
      rw [Nat.div_eq_sub_div (Nat.two_pow_pos w) h, Nat.div_eq_of_lt]
      · decide
      · have : BitVec.toNat x < 2^w + 2^w := by simpa [Nat.pow_succ, Nat.mul_two] using x.isLt
        omega

@[bv_toNat] theorem getLsb_succ_last (x : BitVec (w + 1)) :
    x.getLsb w = decide (2 ^ w ≤ x.toNat) := getLsb_last x

@[bv_toNat] theorem msb_eq_decide (x : BitVec w) : BitVec.msb x = decide (2 ^ (w-1) ≤ x.toNat) := by
  simp [msb_eq_getLsb_last, getLsb_last]

theorem toNat_ge_of_msb_true {x : BitVec n} (p : BitVec.msb x = true) : x.toNat ≥ 2^(n-1) := by
  match n with
  | 0 =>
    simp [BitVec.msb, BitVec.getMsb] at p
  | n + 1 =>
    simp [BitVec.msb_eq_decide] at p
    simp only [Nat.add_sub_cancel]
    exact p

/-! ### cast -/

@[simp, bv_toNat] theorem toNat_cast (h : w = v) (x : BitVec w) : (cast h x).toNat = x.toNat := rfl
@[simp] theorem toFin_cast (h : w = v) (x : BitVec w) :
    (cast h x).toFin = x.toFin.cast (by rw [h]) :=
  rfl

@[simp] theorem getLsb_cast (h : w = v) (x : BitVec w) : (cast h x).getLsb i = x.getLsb i := by
  subst h; simp

@[simp] theorem getMsb_cast (h : w = v) (x : BitVec w) : (cast h x).getMsb i = x.getMsb i := by
  subst h; simp
@[simp] theorem msb_cast (h : w = v) (x : BitVec w) : (cast h x).msb = x.msb := by
  simp [BitVec.msb]

/-! ### toInt/ofInt -/

/-- Prove equality of bitvectors in terms of nat operations. -/
theorem toInt_eq_toNat_cond (i : BitVec n) :
    i.toInt =
      if 2*i.toNat < 2^n then
        (i.toNat : Int)
      else
        (i.toNat : Int) - (2^n : Nat) := by
  unfold BitVec.toInt
  split <;> omega

theorem toInt_eq_toNat_bmod (x : BitVec n) : x.toInt = Int.bmod x.toNat (2^n) := by
  simp only [toInt_eq_toNat_cond]
  split
  case inl g =>
    rw [Int.bmod_pos] <;> simp only [←Int.ofNat_emod, toNat_mod_cancel]
    omega
  case inr g =>
    rw [Int.bmod_neg] <;> simp only [←Int.ofNat_emod, toNat_mod_cancel]
    omega

/-- Prove equality of bitvectors in terms of nat operations. -/
theorem eq_of_toInt_eq {i j : BitVec n} : i.toInt = j.toInt → i = j := by
  intro eq
  simp [toInt_eq_toNat_cond] at eq
  apply eq_of_toNat_eq
  revert eq
  have _ilt := i.isLt
  have _jlt := j.isLt
  split <;> split <;> omega

@[simp] theorem toNat_ofInt {n : Nat} (i : Int) :
  (BitVec.ofInt n i).toNat = (i % (2^n : Nat)).toNat := by
  unfold BitVec.ofInt
  simp

theorem toInt_ofNat {n : Nat} (x : Nat) :
  (BitVec.ofNat n x).toInt = (x : Int).bmod (2^n) := by
  simp [toInt_eq_toNat_bmod]

@[simp] theorem toInt_ofInt {n : Nat} (i : Int) :
  (BitVec.ofInt n i).toInt = i.bmod (2^n) := by
  have _ := Nat.two_pow_pos n
  have p : 0 ≤ i % (2^n : Nat) := by omega
  simp [toInt_eq_toNat_bmod, Int.toNat_of_nonneg p]

/-! ### zeroExtend and truncate -/

@[simp, bv_toNat] theorem toNat_zeroExtend' {m n : Nat} (p : m ≤ n) (x : BitVec m) :
    (zeroExtend' p x).toNat = x.toNat := by
  unfold zeroExtend'
  simp [p, x.isLt, Nat.mod_eq_of_lt]

@[bv_toNat] theorem toNat_zeroExtend (i : Nat) (x : BitVec n) :
    BitVec.toNat (zeroExtend i x) = x.toNat % 2^i := by
  let ⟨x, lt_n⟩ := x
  simp only [zeroExtend]
  if n_le_i : n ≤ i then
    have x_lt_two_i : x < 2 ^ i := lt_two_pow_of_le lt_n n_le_i
    simp [n_le_i, Nat.mod_eq_of_lt, x_lt_two_i]
  else
    simp [n_le_i, toNat_ofNat]

theorem zeroExtend'_eq {x : BitVec w} (h : w ≤ v) : x.zeroExtend' h = x.zeroExtend v := by
  apply eq_of_toNat_eq
  rw [toNat_zeroExtend, toNat_zeroExtend']
  rw [Nat.mod_eq_of_lt]
  exact Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (Nat.zero_lt_two) h)

@[simp, bv_toNat] theorem toNat_truncate (x : BitVec n) : (truncate i x).toNat = x.toNat % 2^i :=
  toNat_zeroExtend i x

@[simp] theorem zeroExtend_eq (x : BitVec n) : zeroExtend n x = x := by
  apply eq_of_toNat_eq
  let ⟨x, lt_n⟩ := x
  simp [truncate, zeroExtend]

@[simp] theorem zeroExtend_zero (m n : Nat) : zeroExtend m (0#n) = 0#m := by
  apply eq_of_toNat_eq
  simp [toNat_zeroExtend]

@[simp] theorem truncate_eq (x : BitVec n) : truncate n x = x := zeroExtend_eq x

@[simp] theorem ofNat_toNat (m : Nat) (x : BitVec n) : x.toNat#m = truncate m x := by
  apply eq_of_toNat_eq
  simp

/-- Moves one-sided left toNat equality to BitVec equality. -/
theorem toNat_eq_nat (x : BitVec w) (y : Nat)
  : (x.toNat = y) ↔ (y < 2^w ∧ (x = y#w)) := by
  apply Iff.intro
  · intro eq
    simp at eq
    have lt := x.isLt
    simp [eq] at lt
    simp [←eq, lt, x.isLt]
  · intro eq
    simp [Nat.mod_eq_of_lt, eq]

/-- Moves one-sided right toNat equality to BitVec equality. -/
theorem nat_eq_toNat (x : BitVec w) (y : Nat)
  : (y = x.toNat) ↔ (y < 2^w ∧ (x = y#w)) := by
  rw [@eq_comm _ _ x.toNat]
  apply toNat_eq_nat

@[simp] theorem getLsb_zeroExtend' (ge : m ≥ n) (x : BitVec n) (i : Nat) :
    getLsb (zeroExtend' ge x) i = getLsb x i := by
  simp [getLsb, toNat_zeroExtend']

@[simp] theorem getLsb_zeroExtend (m : Nat) (x : BitVec n) (i : Nat) :
    getLsb (zeroExtend m x) i = (decide (i < m) && getLsb x i) := by
  simp [getLsb, toNat_zeroExtend, Nat.testBit_mod_two_pow]

@[simp] theorem getMsb_zeroExtend_add {x : BitVec w} (h : k ≤ i) :
    (x.zeroExtend (w + k)).getMsb i = x.getMsb (i - k) := by
  by_cases h : w = 0
  · subst h; simp
  simp only [getMsb, getLsb_zeroExtend]
  by_cases h₁ : i < w + k <;> by_cases h₂ : i - k < w <;> by_cases h₃ : w + k - 1 - i < w + k
    <;> simp [h₁, h₂, h₃]
  · congr 1
    omega
  all_goals (first | apply getLsb_ge | apply Eq.symm; apply getLsb_ge)
    <;> omega

@[simp] theorem getLsb_truncate (m : Nat) (x : BitVec n) (i : Nat) :
    getLsb (truncate m x) i = (decide (i < m) && getLsb x i) :=
  getLsb_zeroExtend m x i

theorem msb_truncate (x : BitVec w) : (x.truncate (k + 1)).msb = x.getLsb k := by
  simp [BitVec.msb, getMsb]

@[simp] theorem zeroExtend_zeroExtend_of_le (x : BitVec w) (h : k ≤ l) :
    (x.zeroExtend l).zeroExtend k = x.zeroExtend k := by
  ext i
  simp only [getLsb_zeroExtend, Fin.is_lt, decide_True, Bool.true_and]
  have p := lt_of_getLsb x i
  revert p
  cases getLsb x i <;> simp; omega

@[simp] theorem truncate_truncate_of_le (x : BitVec w) (h : k ≤ l) :
    (x.truncate l).truncate k = x.truncate k :=
  zeroExtend_zeroExtend_of_le x h

@[simp] theorem truncate_cast {h : w = v} : (cast h x).truncate k = x.truncate k := by
  apply eq_of_getLsb_eq
  simp

theorem msb_zeroExtend (x : BitVec w) : (x.zeroExtend v).msb = (decide (0 < v) && x.getLsb (v - 1)) := by
  rw [msb_eq_getLsb_last]
  simp only [getLsb_zeroExtend]
  cases getLsb x (v - 1) <;> simp; omega

theorem msb_zeroExtend' (x : BitVec w) (h : w ≤ v) : (x.zeroExtend' h).msb = (decide (0 < v) && x.getLsb (v - 1)) := by
  rw [zeroExtend'_eq, msb_zeroExtend]

/-! ## extractLsb -/

@[simp]
protected theorem extractLsb_ofFin {n} (x : Fin (2^n)) (hi lo : Nat) :
  extractLsb hi lo (@BitVec.ofFin n x) = .ofNat (hi-lo+1) (x.val >>> lo) := rfl

@[simp]
protected theorem extractLsb_ofNat (x n : Nat) (hi lo : Nat) :
  extractLsb hi lo x#n = .ofNat (hi - lo + 1) ((x % 2^n) >>> lo) := by
  apply eq_of_getLsb_eq
  intro ⟨i, _lt⟩
  simp [BitVec.ofNat]

@[simp] theorem extractLsb'_toNat (s m : Nat) (x : BitVec n) :
  (extractLsb' s m x).toNat = (x.toNat >>> s) % 2^m := rfl

@[simp] theorem extractLsb_toNat (hi lo : Nat) (x : BitVec n) :
  (extractLsb hi lo x).toNat = (x.toNat >>> lo) % 2^(hi-lo+1) := rfl

@[simp] theorem getLsb_extract (hi lo : Nat) (x : BitVec n) (i : Nat) :
    getLsb (extractLsb hi lo x) i = (i ≤ (hi-lo) && getLsb x (lo+i)) := by
  unfold getLsb
  simp [Nat.lt_succ]

/-! ### allOnes -/

@[simp] theorem toNat_allOnes : (allOnes v).toNat = 2^v - 1 := by
  unfold allOnes
  simp

@[simp] theorem getLsb_allOnes : (allOnes v).getLsb i = decide (i < v) := by
  simp [allOnes]

/-! ### or -/

@[simp] theorem toNat_or (x y : BitVec v) :
    BitVec.toNat (x ||| y) = BitVec.toNat x ||| BitVec.toNat y := rfl

@[simp] theorem toFin_or (x y : BitVec v) :
    BitVec.toFin (x ||| y) = BitVec.toFin x ||| BitVec.toFin y := by
  apply Fin.eq_of_val_eq
  exact (Nat.mod_eq_of_lt <| Nat.or_lt_two_pow x.isLt y.isLt).symm

@[simp] theorem getLsb_or {x y : BitVec v} : (x ||| y).getLsb i = (x.getLsb i || y.getLsb i) := by
  rw [← testBit_toNat, getLsb, getLsb]
  simp

@[simp] theorem getMsb_or {x y : BitVec w} : (x ||| y).getMsb i = (x.getMsb i || y.getMsb i) := by
  simp only [getMsb]
  by_cases h : i < w <;> simp [h]

@[simp] theorem msb_or {x y : BitVec w} : (x ||| y).msb = (x.msb || y.msb) := by
  simp [BitVec.msb]

@[simp] theorem truncate_or {x y : BitVec w} :
    (x ||| y).truncate k = x.truncate k ||| y.truncate k := by
  ext
  simp

/-! ### and -/

@[simp] theorem toNat_and (x y : BitVec v) :
    BitVec.toNat (x &&& y) = BitVec.toNat x &&& BitVec.toNat y := rfl

@[simp] theorem toFin_and (x y : BitVec v) :
    BitVec.toFin (x &&& y) = BitVec.toFin x &&& BitVec.toFin y := by
  apply Fin.eq_of_val_eq
  exact (Nat.mod_eq_of_lt <| Nat.and_lt_two_pow _ y.isLt).symm

@[simp] theorem getLsb_and {x y : BitVec v} : (x &&& y).getLsb i = (x.getLsb i && y.getLsb i) := by
  rw [← testBit_toNat, getLsb, getLsb]
  simp

@[simp] theorem getMsb_and {x y : BitVec w} : (x &&& y).getMsb i = (x.getMsb i && y.getMsb i) := by
  simp only [getMsb]
  by_cases h : i < w <;> simp [h]

@[simp] theorem msb_and {x y : BitVec w} : (x &&& y).msb = (x.msb && y.msb) := by
  simp [BitVec.msb]

@[simp] theorem truncate_and {x y : BitVec w} :
    (x &&& y).truncate k = x.truncate k &&& y.truncate k := by
  ext
  simp

/-! ### xor -/

@[simp] theorem toNat_xor (x y : BitVec v) :
    BitVec.toNat (x ^^^ y) = BitVec.toNat x ^^^ BitVec.toNat y := rfl

@[simp] theorem toFin_xor (x y : BitVec v) :
    BitVec.toFin (x ^^^ y) = BitVec.toFin x ^^^ BitVec.toFin y := by
  apply Fin.eq_of_val_eq
  exact (Nat.mod_eq_of_lt <| Nat.xor_lt_two_pow x.isLt y.isLt).symm

@[simp] theorem getLsb_xor {x y : BitVec v} :
    (x ^^^ y).getLsb i = (xor (x.getLsb i) (y.getLsb i)) := by
  rw [← testBit_toNat, getLsb, getLsb]
  simp

@[simp] theorem truncate_xor {x y : BitVec w} :
    (x ^^^ y).truncate k = x.truncate k ^^^ y.truncate k := by
  ext
  simp

/-! ### not -/

theorem not_def {x : BitVec v} : ~~~x = allOnes v ^^^ x := rfl

@[simp, bv_toNat] theorem toNat_not {x : BitVec v} : (~~~x).toNat = 2^v - 1 - x.toNat := by
  rw [Nat.sub_sub, Nat.add_comm, not_def, toNat_xor]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [toNat_allOnes, Nat.testBit_xor, Nat.testBit_two_pow_sub_one]
  match h : BitVec.toNat x with
  | 0 => simp
  | y+1 =>
    rw [Nat.succ_eq_add_one] at h
    rw [← h]
    rw [Nat.testBit_two_pow_sub_succ (isLt _)]
    · cases w : decide (i < v)
      · simp at w
        simp [w]
        rw [Nat.testBit_lt_two_pow]
        calc BitVec.toNat x < 2 ^ v := isLt _
          _ ≤ 2 ^ i := Nat.pow_le_pow_of_le_right Nat.zero_lt_two w
      · simp

@[simp] theorem toFin_not (x : BitVec w) :
    (~~~x).toFin = x.toFin.rev := by
  apply Fin.val_inj.mp
  simp only [val_toFin, toNat_not, Fin.val_rev]
  omega

@[simp] theorem getLsb_not {x : BitVec v} : (~~~x).getLsb i = (decide (i < v) && ! x.getLsb i) := by
  by_cases h' : i < v <;> simp_all [not_def]

@[simp] theorem truncate_not {x : BitVec w} (h : k ≤ w) :
    (~~~x).truncate k = ~~~(x.truncate k) := by
  ext
  simp [h]
  omega

/-! ### shiftLeft -/

@[simp, bv_toNat] theorem toNat_shiftLeft {x : BitVec v} :
    BitVec.toNat (x <<< n) = BitVec.toNat x <<< n % 2^v :=
  BitVec.toNat_ofNat _ _

@[simp] theorem toFin_shiftLeft {n : Nat} (x : BitVec w) :
    BitVec.toFin (x <<< n) = Fin.ofNat' (x.toNat <<< n) (Nat.two_pow_pos w) := rfl

@[simp] theorem getLsb_shiftLeft (x : BitVec m) (n) :
    getLsb (x <<< n) i = (decide (i < m) && !decide (i < n) && getLsb x (i - n)) := by
  rw [← testBit_toNat, getLsb]
  simp only [toNat_shiftLeft, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft, ge_iff_le]
  -- This step could be a case bashing tactic.
  cases h₁ : decide (i < m) <;> cases h₂ : decide (n ≤ i) <;> cases h₃ : decide (i < n)
  all_goals { simp_all <;> omega }

@[simp] theorem getMsb_shiftLeft (x : BitVec w) (i) :
    (x <<< i).getMsb k = x.getMsb (k + i) := by
  simp only [getMsb, getLsb_shiftLeft]
  by_cases h : w = 0
  · subst h; simp
  have t : w - 1 - k < w := by omega
  simp only [t]
  simp only [decide_True, Nat.sub_sub, Bool.true_and, Nat.add_assoc]
  by_cases h₁ : k < w <;> by_cases h₂ : w - (1 + k) < i <;> by_cases h₃ : k + i < w
    <;> simp [h₁, h₂, h₃]
    <;> (first | apply getLsb_ge | apply Eq.symm; apply getLsb_ge)
    <;> omega

theorem shiftLeftZeroExtend_eq {x : BitVec w} :
    shiftLeftZeroExtend x n = zeroExtend (w+n) x <<< n := by
  apply eq_of_toNat_eq
  rw [shiftLeftZeroExtend, zeroExtend]
  split
  · simp
    rw [Nat.mod_eq_of_lt]
    rw [Nat.shiftLeft_eq, Nat.pow_add]
    exact Nat.mul_lt_mul_of_pos_right x.isLt (Nat.two_pow_pos _)
  · omega

@[simp] theorem getLsb_shiftLeftZeroExtend (x : BitVec m) (n : Nat) :
    getLsb (shiftLeftZeroExtend x n) i = ((! decide (i < n)) && getLsb x (i - n)) := by
  rw [shiftLeftZeroExtend_eq]
  simp only [getLsb_shiftLeft, getLsb_zeroExtend]
  cases h₁ : decide (i < n) <;> cases h₂ : decide (i - n < m + n) <;> cases h₃ : decide (i < m + n)
    <;> simp_all
    <;> (rw [getLsb_ge]; omega)

@[simp] theorem msb_shiftLeftZeroExtend (x : BitVec w) (i : Nat) :
    (shiftLeftZeroExtend x i).msb = x.msb := by
  simp [shiftLeftZeroExtend_eq, BitVec.msb]

/-! ### ushiftRight -/

@[simp, bv_toNat] theorem toNat_ushiftRight (x : BitVec n) (i : Nat) :
    (x >>> i).toNat = x.toNat >>> i := rfl

@[simp] theorem getLsb_ushiftRight (x : BitVec n) (i j : Nat) :
    getLsb (x >>> i) j = getLsb x (i+j) := by
  unfold getLsb ; simp

/-! ### append -/

theorem append_def (x : BitVec v) (y : BitVec w) :
    x ++ y = (shiftLeftZeroExtend x w ||| zeroExtend' (Nat.le_add_left w v) y) := rfl

@[simp] theorem toNat_append (x : BitVec m) (y : BitVec n) :
    (x ++ y).toNat = x.toNat <<< n ||| y.toNat :=
  rfl

@[simp] theorem getLsb_append {v : BitVec n} {w : BitVec m} :
    getLsb (v ++ w) i = bif i < m then getLsb w i else getLsb v (i - m) := by
  simp [append_def]
  by_cases h : i < m
  · simp [h]
  · simp [h]; simp_all

theorem msb_append {x : BitVec w} {y : BitVec v} :
    (x ++ y).msb = bif (w == 0) then (y.msb) else (x.msb) := by
  rw [← append_eq, append]
  simp [msb_zeroExtend']
  by_cases h : w = 0
  · subst h
    simp [BitVec.msb, getMsb]
  · rw [cond_eq_if]
    have q : 0 < w + v := by omega
    have t : y.getLsb (w + v - 1) = false := getLsb_ge _ _ (by omega)
    simp [h, q, t, BitVec.msb, getMsb]

@[simp] theorem truncate_append {x : BitVec w} {y : BitVec v} :
    (x ++ y).truncate k = if h : k ≤ v then y.truncate k else (x.truncate (k - v) ++ y).cast (by omega) := by
  apply eq_of_getLsb_eq
  intro i
  simp only [getLsb_zeroExtend, Fin.is_lt, decide_True, getLsb_append, Bool.true_and]
  split
  · have t : i < v := by omega
    simp [t]
  · by_cases t : i < v
    · simp [t]
    · have t' : i - v < k - v := by omega
      simp [t, t']

@[simp] theorem truncate_cons {x : BitVec w} : (cons a x).truncate w = x := by
  simp [cons]

/-! ### rev -/

theorem getLsb_rev (x : BitVec w) (i : Fin w) :
    x.getLsb i.rev = x.getMsb i := by
  simp [getLsb, getMsb]
  congr 1
  omega

theorem getMsb_rev (x : BitVec w) (i : Fin w) :
    x.getMsb i.rev = x.getLsb i := by
  simp only [← getLsb_rev]
  simp only [Fin.rev]
  congr
  omega

/-! ### cons -/

@[simp] theorem toNat_cons (b : Bool) (x : BitVec w) :
    (cons b x).toNat = (b.toNat <<< w) ||| x.toNat := by
  let ⟨x, _⟩ := x
  simp [cons, toNat_append, toNat_ofBool]

/-- Variant of `toNat_cons` using `+` instead of `|||`. -/
theorem toNat_cons' {x : BitVec w} :
    (cons a x).toNat = (a.toNat <<< w) + x.toNat := by
  simp [cons, Nat.shiftLeft_eq, Nat.mul_comm _ (2^w), Nat.mul_add_lt_is_or, x.isLt]

@[simp] theorem getLsb_cons (b : Bool) {n} (x : BitVec n) (i : Nat) :
    getLsb (cons b x) i = if i = n then b else getLsb x i := by
  simp only [getLsb, toNat_cons, Nat.testBit_or]
  rw [Nat.testBit_shiftLeft]
  rcases Nat.lt_trichotomy i n with i_lt_n | i_eq_n | n_lt_i
  · have p1 : ¬(n ≤ i) := by omega
    have p2 : i ≠ n := by omega
    simp [p1, p2]
  · simp [i_eq_n, testBit_toNat]
    cases b <;> trivial
  · have p1 : i ≠ n := by omega
    have p2 : i - n ≠ 0 := by omega
    simp [p1, p2, Nat.testBit_bool_to_nat]

@[simp] theorem msb_cons : (cons a x).msb = a := by
  simp [cons, msb_cast, msb_append]

theorem truncate_succ (x : BitVec w) :
    truncate (i+1) x = cons (getLsb x i) (truncate i x) := by
  apply eq_of_getLsb_eq
  intro j
  simp only [getLsb_truncate, getLsb_cons, j.isLt, decide_True, Bool.true_and]
  if j_eq : j.val = i then
    simp [j_eq]
  else
    have j_lt : j.val < i := Nat.lt_of_le_of_ne (Nat.le_of_succ_le_succ j.isLt) j_eq
    simp [j_eq, j_lt]

theorem eq_msb_cons_truncate (x : BitVec (w+1)) : x = (cons x.msb (x.truncate w)) := by
  ext i
  simp
  split <;> rename_i h
  · simp [BitVec.msb, getMsb, h]
  · by_cases h' : i < w
    · simp_all
    · omega

/-! ### concat -/

@[simp] theorem toNat_concat (x : BitVec w) (b : Bool) :
    (concat x b).toNat = x.toNat * 2 + b.toNat := by
  apply Nat.eq_of_testBit_eq
  simp only [concat, toNat_append, Nat.shiftLeft_eq, Nat.pow_one, toNat_ofBool, Nat.testBit_or]
  cases b
  · simp
  · rintro (_ | i)
    <;> simp [Nat.add_mod, Nat.add_comm, Nat.add_mul_div_right]

theorem getLsb_concat (x : BitVec w) (b : Bool) (i : Nat) :
    (concat x b).getLsb i = if i = 0 then b else x.getLsb (i - 1) := by
  simp only [concat, getLsb, toNat_append, toNat_ofBool, Nat.testBit_or, Nat.shiftLeft_eq]
  cases i
  · simp [Nat.mod_eq_of_lt b.toNat_lt]
  · simp [Nat.div_eq_of_lt b.toNat_lt]

@[simp] theorem getLsb_concat_zero : (concat x b).getLsb 0 = b := by
  simp [getLsb_concat]

@[simp] theorem getLsb_concat_succ : (concat x b).getLsb (i + 1) = x.getLsb i := by
  simp [getLsb_concat]

@[simp] theorem not_concat (x : BitVec w) (b : Bool) : ~~~(concat x b) = concat (~~~x) !b := by
  ext i; cases i using Fin.succRecOn <;> simp [*, Nat.succ_lt_succ]

@[simp] theorem concat_or_concat (x y : BitVec w) (a b : Bool) :
    (concat x a) ||| (concat y b) = concat (x ||| y) (a || b) := by
  ext i; cases i using Fin.succRecOn <;> simp

@[simp] theorem concat_and_concat (x y : BitVec w) (a b : Bool) :
    (concat x a) &&& (concat y b) = concat (x &&& y) (a && b) := by
  ext i; cases i using Fin.succRecOn <;> simp

@[simp] theorem concat_xor_concat (x y : BitVec w) (a b : Bool) :
    (concat x a) ^^^ (concat y b) = concat (x ^^^ y) (xor a b) := by
  ext i; cases i using Fin.succRecOn <;> simp

/-! ### add -/

theorem add_def {n} (x y : BitVec n) : x + y = .ofNat n (x.toNat + y.toNat) := rfl

/--
Definition of bitvector addition as a nat.
-/
@[simp, bv_toNat] theorem toNat_add (x y : BitVec w) : (x + y).toNat = (x.toNat + y.toNat) % 2^w := rfl
@[simp] theorem toFin_add (x y : BitVec w) : (x + y).toFin = toFin x + toFin y := rfl
@[simp] theorem ofFin_add (x : Fin (2^n)) (y : BitVec n) :
  .ofFin x + y = .ofFin (x + y.toFin) := rfl
@[simp] theorem add_ofFin (x : BitVec n) (y : Fin (2^n)) :
  x + .ofFin y = .ofFin (x.toFin + y) := rfl
@[simp] theorem ofNat_add_ofNat {n} (x y : Nat) : x#n + y#n = (x + y)#n := by
  apply eq_of_toNat_eq ; simp [BitVec.ofNat]

protected theorem add_assoc (x y z : BitVec n) : x + y + z = x + (y + z) := by
  apply eq_of_toNat_eq ; simp [Nat.add_assoc]

protected theorem add_comm (x y : BitVec n) : x + y = y + x := by
  simp [add_def, Nat.add_comm]

@[simp] protected theorem add_zero (x : BitVec n) : x + 0#n = x := by simp [add_def]

@[simp] protected theorem zero_add (x : BitVec n) : 0#n + x = x := by simp [add_def]

theorem truncate_add (x y : BitVec w) (h : i ≤ w) :
    (x + y).truncate i = x.truncate i + y.truncate i := by
  have dvd : 2^i ∣ 2^w := Nat.pow_dvd_pow _ h
  simp [bv_toNat, h, Nat.mod_mod_of_dvd _ dvd]

/-! ### sub/neg -/

theorem sub_def {n} (x y : BitVec n) : x - y = .ofNat n (x.toNat + (2^n - y.toNat)) := by rfl

@[simp, bv_toNat] theorem toNat_sub {n} (x y : BitVec n) :
  (x - y).toNat = ((x.toNat + (2^n - y.toNat)) % 2^n) := rfl
@[simp] theorem toFin_sub (x y : BitVec n) : (x - y).toFin = toFin x - toFin y := rfl

@[simp] theorem ofFin_sub (x : Fin (2^n)) (y : BitVec n) : .ofFin x - y = .ofFin (x - y.toFin) :=
  rfl
@[simp] theorem sub_ofFin (x : BitVec n) (y : Fin (2^n)) : x - .ofFin y = .ofFin (x.toFin - y) :=
  rfl
-- Remark: we don't use `[simp]` here because simproc` subsumes it for literals.
-- If `x` and `n` are not literals, applying this theorem eagerly may not be a good idea.
theorem ofNat_sub_ofNat {n} (x y : Nat) : x#n - y#n = .ofNat n (x + (2^n - y % 2^n)) := by
  apply eq_of_toNat_eq ; simp [BitVec.ofNat]

@[simp] protected theorem sub_zero (x : BitVec n) : x - (0#n) = x := by apply eq_of_toNat_eq ; simp

@[simp] protected theorem sub_self (x : BitVec n) : x - x = 0#n := by
  apply eq_of_toNat_eq
  simp only [toNat_sub]
  rw [Nat.add_sub_of_le]
  · simp
  · exact Nat.le_of_lt x.isLt

@[simp, bv_toNat] theorem toNat_neg (x : BitVec n) : (- x).toNat = (2^n - x.toNat) % 2^n := by
  simp [Neg.neg, BitVec.neg]

theorem sub_toAdd {n} (x y : BitVec n) : x - y = x + - y := by
  apply eq_of_toNat_eq
  simp

@[simp] theorem neg_zero (n:Nat) : -0#n = 0#n := by apply eq_of_toNat_eq ; simp

theorem add_sub_cancel (x y : BitVec w) : x + y - y = x := by
  apply eq_of_toNat_eq
  have y_toNat_le := Nat.le_of_lt y.toNat_lt
  rw [toNat_sub, toNat_add, Nat.mod_add_mod, Nat.add_assoc, ← Nat.add_sub_assoc y_toNat_le,
    Nat.add_sub_cancel_left, Nat.add_mod_right, toNat_mod_cancel]

theorem negOne_eq_allOnes : -1#w = allOnes w := by
  apply eq_of_toNat_eq
  if g : w = 0 then
    simp [g]
  else
    have q : 1 < 2^w := by simp [g]
    have r : (2^w - 1) < 2^w := by omega
    simp [Nat.mod_eq_of_lt q, Nat.mod_eq_of_lt r]

/-! ### mul -/

theorem mul_def {n} {x y : BitVec n} : x * y = (ofFin <| x.toFin * y.toFin) := by rfl

@[simp, bv_toNat] theorem toNat_mul (x y : BitVec n) : (x * y).toNat = (x.toNat * y.toNat) % 2 ^ n := rfl
@[simp] theorem toFin_mul (x y : BitVec n) : (x * y).toFin = (x.toFin * y.toFin) := rfl

protected theorem mul_comm (x y : BitVec w) : x * y = y * x := by
  apply eq_of_toFin_eq; simpa using Fin.mul_comm ..
instance : Std.Commutative (fun (x y : BitVec w) => x * y) := ⟨BitVec.mul_comm⟩

protected theorem mul_assoc (x y z : BitVec w) : x * y * z = x * (y * z) := by
  apply eq_of_toFin_eq; simpa using Fin.mul_assoc ..
instance : Std.Associative (fun (x y : BitVec w) => x * y) := ⟨BitVec.mul_assoc⟩

@[simp] protected theorem mul_one (x : BitVec w) : x * 1#w = x := by
  cases w
  · apply Subsingleton.elim
  · apply eq_of_toNat_eq; simp [Nat.mod_eq_of_lt]

@[simp] protected theorem one_mul (x : BitVec w) : 1#w * x = x := by
  rw [BitVec.mul_comm, BitVec.mul_one]

instance : Std.LawfulCommIdentity (fun (x y : BitVec w) => x * y) (1#w) where
  right_id := BitVec.mul_one

/-! ### le and lt -/

@[bv_toNat] theorem le_def (x y : BitVec n) :
  x ≤ y ↔ x.toNat ≤ y.toNat := Iff.rfl

@[simp] theorem le_ofFin (x : BitVec n) (y : Fin (2^n)) :
  x ≤ BitVec.ofFin y ↔ x.toFin ≤ y := Iff.rfl
@[simp] theorem ofFin_le (x : Fin (2^n)) (y : BitVec n) :
  BitVec.ofFin x ≤ y ↔ x ≤ y.toFin := Iff.rfl
@[simp] theorem ofNat_le_ofNat {n} (x y : Nat) : (x#n) ≤ (y#n) ↔ x % 2^n ≤ y % 2^n := by
  simp [le_def]

@[bv_toNat] theorem lt_def (x y : BitVec n) :
  x < y ↔ x.toNat < y.toNat := Iff.rfl

@[simp] theorem lt_ofFin (x : BitVec n) (y : Fin (2^n)) :
  x < BitVec.ofFin y ↔ x.toFin < y := Iff.rfl
@[simp] theorem ofFin_lt (x : Fin (2^n)) (y : BitVec n) :
  BitVec.ofFin x < y ↔ x < y.toFin := Iff.rfl
@[simp] theorem ofNat_lt_ofNat {n} (x y : Nat) : (x#n) < (y#n) ↔ x % 2^n < y % 2^n := by
  simp [lt_def]

protected theorem lt_of_le_ne (x y : BitVec n) (h1 : x <= y) (h2 : ¬ x = y) : x < y := by
  revert h1 h2
  let ⟨x, lt⟩ := x
  let ⟨y, lt⟩ := y
  simp
  exact Nat.lt_of_le_of_ne

/- ! ### intMax -/

/-- The bitvector of width `w` that has the largest value when interpreted as an integer. -/
def intMax (w : Nat) : BitVec w  := (2^w - 1)#w

theorem getLsb_intMax_eq (w : Nat) : (intMax w).getLsb i = decide (i < w) := by
  simp [intMax, getLsb]

theorem toNat_intMax_eq : (intMax w).toNat = 2^w - 1 := by
  have h : 2^w - 1 < 2^w := by
    have pos : 2^w > 0 := Nat.pow_pos (by decide)
    omega
  simp [intMax, Nat.shiftLeft_eq, Nat.one_mul, natCast_eq_ofNat, toNat_ofNat, Nat.mod_eq_of_lt h]

end BitVec
