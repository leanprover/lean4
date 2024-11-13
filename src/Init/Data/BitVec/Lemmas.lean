/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix, Harun Khan, Alex Keizer, Abdalrhman M Mohamed, Siddharth Bhat

-/
prelude
import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.Int.Pow

set_option linter.missingDocs true

namespace BitVec

@[simp] theorem getLsbD_ofFin (x : Fin (2^n)) (i : Nat) :
    getLsbD (BitVec.ofFin x) i = x.val.testBit i := rfl

@[simp] theorem getLsbD_ge (x : BitVec w) (i : Nat) (ge : w ≤ i) : getLsbD x i = false := by
  let ⟨x, x_lt⟩ := x
  simp only [getLsbD_ofFin]
  apply Nat.testBit_lt_two_pow
  have p : 2^w ≤ 2^i := Nat.pow_le_pow_of_le_right (by omega) ge
  omega

@[simp] theorem getMsbD_ge (x : BitVec w) (i : Nat) (ge : w ≤ i) : getMsbD x i = false := by
  rw [getMsbD]
  simp only [Bool.and_eq_false_imp, decide_eq_true_eq]
  omega

theorem lt_of_getLsbD {x : BitVec w} {i : Nat} : getLsbD x i = true → i < w := by
  if h : i < w then
    simp [h]
  else
    simp [Nat.ge_of_not_lt h]

theorem lt_of_getMsbD {x : BitVec w} {i : Nat} : getMsbD x i = true → i < w := by
  if h : i < w then
    simp [h]
  else
    simp [Nat.ge_of_not_lt h]

@[simp] theorem getElem?_eq_getElem {l : BitVec w} {n} (h : n < w) : l[n]? = some l[n] := by
  simp only [getElem?_def, h, ↓reduceDIte]

theorem getElem?_eq_some {l : BitVec w} : l[n]? = some a ↔ ∃ h : n < w, l[n] = a := by
  simp only [getElem?_def]
  split
  · simp_all
  · simp; omega

@[simp] theorem getElem?_eq_none_iff {l : BitVec w} : l[n]? = none ↔ w ≤ n := by
  simp only [getElem?_def]
  split
  · simp_all
  · simp; omega

theorem getElem?_eq_none {l : BitVec w} (h : w ≤ n) : l[n]? = none := getElem?_eq_none_iff.mpr h

theorem getElem?_eq (l : BitVec w) (i : Nat) :
    l[i]? = if h : i < w then some l[i] else none := by
  split <;> simp_all

@[simp] theorem some_getElem_eq_getElem? (l : BitVec w) (i : Nat) (h : i < w) :
    (some l[i] = l[i]?) ↔ True := by
  simp [h]

@[simp] theorem getElem?_eq_some_getElem (l : BitVec w) (i : Nat) (h : i < w) :
    (l[i]? = some l[i]) ↔ True := by
  simp [h]

theorem getElem_eq_iff {l : BitVec w} {n : Nat} {h : n < w} : l[n] = x ↔ l[n]? = some x := by
  simp only [getElem?_eq_some]
  exact ⟨fun w => ⟨h, w⟩, fun h => h.2⟩

theorem getElem_eq_getElem? (l : BitVec w) (i : Nat) (h : i < w) :
    l[i] = l[i]?.get (by simp [getElem?_eq_getElem, h]) := by
  simp [getElem_eq_iff]

theorem getLsbD_eq_getElem?_getD {x : BitVec w} {i : Nat} :
    x.getLsbD i = x[i]?.getD false := by
  rw [getElem?_def]
  split
  · rfl
  · simp_all

/--
This normalized a bitvec using `ofFin` to `ofNat`.
-/
theorem ofFin_eq_ofNat : @BitVec.ofFin w (Fin.mk x lt) = BitVec.ofNat w x := by
  simp only [BitVec.ofNat, Fin.ofNat', lt, Nat.mod_eq_of_lt]

/-- Prove equality of bitvectors in terms of nat operations. -/
theorem eq_of_toNat_eq {n} : ∀ {x y : BitVec n}, x.toNat = y.toNat → x = y
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

@[simp] theorem val_toFin (x : BitVec w) : x.toFin.val = x.toNat := rfl

@[bv_toNat] theorem toNat_eq {x y : BitVec n} : x = y ↔ x.toNat = y.toNat :=
  Iff.intro (congrArg BitVec.toNat) eq_of_toNat_eq

@[bv_toNat] theorem toNat_ne {x y : BitVec n} : x ≠ y ↔ x.toNat ≠ y.toNat := by
  rw [Ne, toNat_eq]

theorem testBit_toNat (x : BitVec w) : x.toNat.testBit i = x.getLsbD i := rfl

theorem getMsb'_eq_getLsb' (x : BitVec w) (i : Fin w) :
    x.getMsb' i = x.getLsb' ⟨w - 1 - i, by omega⟩ := by
  simp only [getMsb', getLsb']

theorem getMsb?_eq_getLsb? (x : BitVec w) (i : Nat) :
    x.getMsb? i = if i < w then x.getLsb? (w - 1 - i) else none := by
  simp only [getMsb?, getLsb?_eq_getElem?]
  split <;> simp [getMsb'_eq_getLsb']

theorem getMsbD_eq_getLsbD (x : BitVec w) (i : Nat) : x.getMsbD i = (decide (i < w) && x.getLsbD (w - 1 - i)) := by
  rw [getMsbD, getLsbD]

theorem getLsbD_eq_getMsbD (x : BitVec w) (i : Nat) : x.getLsbD i = (decide (i < w) && x.getMsbD (w - 1 - i)) := by
  rw [getMsbD]
  by_cases h₁ : i < w <;> by_cases h₂ : w - 1 - i < w <;>
    simp only [h₁, h₂] <;> simp only [decide_true, decide_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true]
  · congr
    omega
  all_goals
    apply getLsbD_ge
    omega

@[simp] theorem getLsb?_ge (x : BitVec w) (i : Nat) (ge : w ≤ i) : x[i]? = none := by
  simp [ge]

@[simp] theorem getMsb?_ge (x : BitVec w) (i : Nat) (ge : w ≤ i) : getMsb? x i = none := by
  simp [getMsb?_eq_getLsb?]; omega

theorem lt_of_getLsb?_eq_some (x : BitVec w) (i : Nat) : x[i]? = some b → i < w := by
  cases h : x[i]? with
  | none => simp
  | some => by_cases i < w <;> simp_all

theorem lt_of_getMsb?_eq_some (x : BitVec w) (i : Nat) : getMsb? x i = some b → i < w := by
  if h : i < w then
    simp [h]
  else
    simp [Nat.ge_of_not_lt h]

theorem lt_of_getLsb?_isSome (x : BitVec w) (i : Nat) : x[i]?.isSome → i < w := by
  cases h : x[i]? with
  | none => simp
  | some => by_cases i < w <;> simp_all

theorem lt_of_getMsb?_isSome (x : BitVec w) (i : Nat) : (getMsb? x i).isSome → i < w := by
  if h : i < w then
    simp [h]
  else
    simp [Nat.ge_of_not_lt h]

theorem getMsbD_eq_getMsb?_getD (x : BitVec w) (i : Nat) :
    x.getMsbD i = (x.getMsb? i).getD false := by
  rw [getMsbD_eq_getLsbD]
  by_cases h : w = 0
  · simp [getMsb?, h]
  · rw [getLsbD_eq_getElem?_getD, getMsb?_eq_getLsb?]
    split <;>
    · simp only [getLsb?_eq_getElem?, Bool.and_iff_right_iff_imp, decide_eq_true_eq,
        Option.getD_none, Bool.and_eq_false_imp]
      intros
      omega

-- We choose `eq_of_getLsbD_eq` as the `@[ext]` theorem for `BitVec`
-- somewhat arbitrarily over `eq_of_getMsbD_eq`.
@[ext] theorem eq_of_getLsbD_eq {x y : BitVec w}
    (pred : ∀(i : Fin w), x.getLsbD i.val = y.getLsbD i.val) : x = y := by
  apply eq_of_toNat_eq
  apply Nat.eq_of_testBit_eq
  intro i
  if i_lt : i < w then
    exact pred ⟨i, i_lt⟩
  else
    have p : i ≥ w := Nat.le_of_not_gt i_lt
    simp [testBit_toNat, getLsbD_ge _ _ p]

theorem eq_of_getMsbD_eq {x y : BitVec w}
    (pred : ∀(i : Fin w), x.getMsbD i.val = y.getMsbD i.val) : x = y := by
  simp only [getMsbD] at pred
  apply eq_of_getLsbD_eq
  intro ⟨i, i_lt⟩
  if w_zero : w = 0 then
    simp [w_zero]
  else
    have w_pos := Nat.pos_of_ne_zero w_zero
    have r : i ≤ w - 1 := by
      simp [Nat.le_sub_iff_add_le w_pos]
      exact i_lt
    have q_lt : w - 1 - i < w := by
      simp only [Nat.sub_sub]
      apply Nat.sub_lt w_pos
      simp [Nat.succ_add]
    have q := pred ⟨w - 1 - i, q_lt⟩
    simpa [q_lt, Nat.sub_sub_self, r] using q

-- This cannot be a `@[simp]` lemma, as it would be tried at every term.
theorem of_length_zero {x : BitVec 0} : x = 0#0 := by ext; simp

theorem toNat_zero_length (x : BitVec 0) : x.toNat = 0 := by simp [of_length_zero]
theorem getLsbD_zero_length (x : BitVec 0) : x.getLsbD i = false := by simp
theorem getMsbD_zero_length (x : BitVec 0) : x.getMsbD i = false := by simp
theorem msb_zero_length (x : BitVec 0) : x.msb = false := by simp [BitVec.msb, of_length_zero]

theorem toNat_of_zero_length (h : w = 0) (x : BitVec w) : x.toNat = 0 := by
  subst h; simp [toNat_zero_length]
theorem getLsbD_of_zero_length (h : w = 0) (x : BitVec w) : x.getLsbD i = false := by
  subst h; simp [getLsbD_zero_length]
theorem getMsbD_of_zero_length (h : w = 0) (x : BitVec w) : x.getMsbD i = false := by
  subst h; simp [getMsbD_zero_length]
theorem msb_of_zero_length (h : w = 0) (x : BitVec w) : x.msb = false := by
  subst h; simp [msb_zero_length]

theorem ofFin_ofNat (n : Nat) :
    ofFin (no_index (OfNat.ofNat n : Fin (2^w))) = OfNat.ofNat n := by
  simp only [OfNat.ofNat, Fin.ofNat', BitVec.ofNat, Nat.and_pow_two_sub_one_eq_mod]

theorem eq_of_toFin_eq : ∀ {x y : BitVec w}, x.toFin = y.toFin → x = y
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

theorem toFin_inj {x y : BitVec w} : x.toFin = y.toFin ↔ x = y := by
  apply Iff.intro
  case mp =>
    exact @eq_of_toFin_eq w x y
  case mpr =>
    intro h
    simp [toFin, h]

theorem toFin_zero : toFin (0 : BitVec w) = 0 := rfl
theorem toFin_one  : toFin (1 : BitVec w) = 1 := by
  rw [toFin_inj]; simp only [ofNat_eq_ofNat, ofFin_ofNat]

@[simp] theorem toNat_ofBool (b : Bool) : (ofBool b).toNat = b.toNat := by
  cases b <;> rfl

@[simp] theorem msb_ofBool (b : Bool) : (ofBool b).msb = b := by
  cases b <;> simp [BitVec.msb, getMsbD, getLsbD]

theorem ofNat_one (n : Nat) : BitVec.ofNat 1 n = BitVec.ofBool (n % 2 = 1) :=  by
  rcases (Nat.mod_two_eq_zero_or_one n) with h | h <;> simp [h, BitVec.ofNat, Fin.ofNat']

theorem ofBool_eq_iff_eq : ∀ {b b' : Bool}, BitVec.ofBool b = BitVec.ofBool b' ↔ b = b' := by
  decide

@[simp] theorem not_ofBool : ~~~ (ofBool b) = ofBool (!b) := by cases b <;> rfl

@[simp] theorem ofBool_and_ofBool : ofBool b &&& ofBool b' = ofBool (b && b') := by
  cases b <;> cases b' <;> rfl

@[simp] theorem ofBool_or_ofBool : ofBool b ||| ofBool b' = ofBool (b || b') := by
  cases b <;> cases b' <;> rfl

@[simp] theorem ofBool_xor_ofBool : ofBool b ^^^ ofBool b' = ofBool (b ^^ b') := by
  cases b <;> cases b' <;> rfl

@[simp, bv_toNat] theorem toNat_ofFin (x : Fin (2^n)) : (BitVec.ofFin x).toNat = x.val := rfl

@[simp] theorem toNat_ofNatLt (x : Nat) (p : x < 2^w) : (x#'p).toNat = x := rfl

@[simp] theorem getLsbD_ofNatLt {n : Nat} (x : Nat) (lt : x < 2^n) (i : Nat) :
  getLsbD (x#'lt) i = x.testBit i := by
  simp [getLsbD, BitVec.ofNatLt]

@[simp, bv_toNat] theorem toNat_ofNat (x w : Nat) : (BitVec.ofNat w x).toNat = x % 2^w := by
  simp [BitVec.toNat, BitVec.ofNat, Fin.ofNat']

@[simp] theorem toFin_ofNat (x : Nat) : toFin (BitVec.ofNat w x) = Fin.ofNat' (2^w) x := rfl

-- Remark: we don't use `[simp]` here because simproc` subsumes it for literals.
-- If `x` and `n` are not literals, applying this theorem eagerly may not be a good idea.
theorem getLsbD_ofNat (n : Nat) (x : Nat) (i : Nat) :
  getLsbD (BitVec.ofNat n x) i = (i < n && x.testBit i) := by
  simp [getLsbD, BitVec.ofNat, Fin.val_ofNat']

@[simp] theorem getLsbD_zero : (0#w).getLsbD i = false := by simp [getLsbD]

@[simp] theorem getElem_zero (h : i < w) : (0#w)[i] = false := by simp [getElem_eq_testBit_toNat]

@[simp] theorem getMsbD_zero : (0#w).getMsbD i = false := by simp [getMsbD]

@[simp] theorem getLsbD_one : (1#w).getLsbD i = (decide (0 < w) && decide (i = 0)) := by
  simp only [getLsbD, toNat_ofNat, Nat.testBit_mod_two_pow]
  by_cases h : i = 0
    <;> simp [h, Nat.testBit_to_div_mod, Nat.div_eq_of_lt]

@[simp] theorem getElem_one (h : i < w) : (1#w)[i] = decide (i = 0) := by
  simp [← getLsbD_eq_getElem, getLsbD_one, h, show 0 < w by omega]

/-- The msb at index `w-1` is the least significant bit, and is true when the width is nonzero. -/
@[simp] theorem getMsbD_one : (1#w).getMsbD i = (decide (i = w - 1) && decide (0 < w)) := by
  simp only [getMsbD]
  by_cases h : 0 < w <;> by_cases h' : i = w - 1 <;> simp [h, h'] <;> omega

@[simp] theorem toNat_mod_cancel (x : BitVec n) : x.toNat % (2^n) = x.toNat :=
  Nat.mod_eq_of_lt x.isLt

@[simp] theorem toNat_mod_cancel' {x : BitVec n} :
    (x.toNat : Int) % (((2 ^ n) : Nat) : Int) = x.toNat := by
  rw_mod_cast [toNat_mod_cancel]

@[simp] theorem sub_toNat_mod_cancel {x : BitVec w} (h : ¬ x = 0#w) :
    (2 ^ w - x.toNat) % 2 ^ w = 2 ^ w - x.toNat := by
  simp only [toNat_eq, toNat_ofNat, Nat.zero_mod] at h
  rw [Nat.mod_eq_of_lt (by omega)]

@[simp] theorem sub_sub_toNat_cancel {x : BitVec w} :
    2 ^ w - (2 ^ w - x.toNat) = x.toNat := by
  simp [Nat.sub_sub_eq_min, Nat.min_eq_right]
  omega

@[simp] theorem sub_add_bmod_cancel {x y : BitVec w} :
    ((((2 ^ w : Nat) - y.toNat) : Int) + x.toNat).bmod (2 ^ w) =
      ((x.toNat : Int) - y.toNat).bmod (2 ^ w) := by
  rw [Int.sub_eq_add_neg, Int.add_assoc, Int.add_comm, Int.bmod_add_cancel, Int.add_comm,
    Int.sub_eq_add_neg]

private theorem lt_two_pow_of_le {x m n : Nat} (lt : x < 2 ^ m) (le : m ≤ n) : x < 2 ^ n :=
  Nat.lt_of_lt_of_le lt (Nat.pow_le_pow_of_le_right (by trivial : 0 < 2) le)

@[simp] theorem getElem_zero_ofNat_zero (i : Nat) (h : i < w) : (BitVec.ofNat w 0)[i] = false := by
  simp [getElem_eq_testBit_toNat]

@[simp] theorem getElem_zero_ofNat_one (h : 0 < w) : (BitVec.ofNat w 1)[0] = true := by
  simp [getElem_eq_testBit_toNat, h]

theorem getElem?_zero_ofNat_zero : (BitVec.ofNat (w+1) 0)[0]? = some false := by
  simp

theorem getElem?_zero_ofNat_one : (BitVec.ofNat (w+1) 1)[0]? = some true := by
  simp

-- This does not need to be a `@[simp]` theorem as it is already handled by `getElem?_eq_getElem`.
theorem getElem?_zero_ofBool (b : Bool) : (ofBool b)[0]? = some b := by
  simp only [ofBool, ofNat_eq_ofNat, cond_eq_if]
  split <;> simp_all

@[simp] theorem getElem_zero_ofBool (b : Bool) : (ofBool b)[0] = b := by
  rw [getElem_eq_iff, getElem?_zero_ofBool]

theorem getElem?_succ_ofBool (b : Bool) (i : Nat) : (ofBool b)[i + 1]? = none := by
  simp

@[simp]
theorem getLsbD_ofBool (b : Bool) (i : Nat) : (ofBool b).getLsbD i = ((i = 0) && b) := by
  rcases b with rfl | rfl
  · simp [ofBool]
  · simp only [ofBool, ofNat_eq_ofNat, cond_true, getLsbD_ofNat, Bool.and_true]
    by_cases hi : i = 0 <;> simp [hi] <;> omega

@[simp]
theorem getElem_ofBool {b : Bool} {i : Nat} : (ofBool b)[0] = b := by
  rcases b with rfl | rfl
  · simp [ofBool]
  · simp only [ofBool]
    by_cases hi : i = 0 <;> simp [hi] <;> omega

/-! ### msb -/

@[simp] theorem msb_zero : (0#w).msb = false := by simp [BitVec.msb, getMsbD]

@[simp] theorem msb_one : (1#w).msb = decide (w = 1) := by
  simp [BitVec.msb, getMsbD_one, ← Bool.decide_and]
  omega

theorem msb_eq_getLsbD_last (x : BitVec w) :
    x.msb = x.getLsbD (w - 1) := by
  simp only [BitVec.msb, getMsbD]
  rcases w  with rfl | w
  · simp [BitVec.eq_nil x]
  · simp

@[bv_toNat] theorem getLsbD_last (x : BitVec w) :
    x.getLsbD (w-1) = decide (2 ^ (w-1) ≤ x.toNat) := by
  rcases w with rfl | w
  · simp [toNat_of_zero_length]
  · simp only [getLsbD, Nat.testBit_to_div_mod, Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
    rcases (Nat.lt_or_ge (BitVec.toNat x) (2 ^ w)) with h | h
    · simp [Nat.div_eq_of_lt h, h]
    · simp only [h]
      rw [Nat.div_eq_sub_div (Nat.two_pow_pos w) h, Nat.div_eq_of_lt]
      · simp
      · omega

@[bv_toNat] theorem getLsbD_succ_last (x : BitVec (w + 1)) :
    x.getLsbD w = decide (2 ^ w ≤ x.toNat) := getLsbD_last x

@[bv_toNat] theorem msb_eq_decide (x : BitVec w) : BitVec.msb x = decide (2 ^ (w-1) ≤ x.toNat) := by
  simp [msb_eq_getLsbD_last, getLsbD_last]

theorem toNat_ge_of_msb_true {x : BitVec n} (p : BitVec.msb x = true) : x.toNat ≥ 2^(n-1) := by
  match n with
  | 0 =>
    simp [BitVec.msb, BitVec.getMsbD] at p
  | n + 1 =>
    simp only [msb_eq_decide, Nat.add_one_sub_one, decide_eq_true_eq] at p
    simp only [Nat.add_sub_cancel]
    exact p

/-! ### cast -/

@[simp, bv_toNat] theorem toNat_cast (h : w = v) (x : BitVec w) : (cast h x).toNat = x.toNat := rfl
@[simp] theorem toFin_cast (h : w = v) (x : BitVec w) :
    (cast h x).toFin = x.toFin.cast (by rw [h]) :=
  rfl

@[simp] theorem getLsbD_cast (h : w = v) (x : BitVec w) : (cast h x).getLsbD i = x.getLsbD i := by
  subst h; simp

@[simp] theorem getMsbD_cast (h : w = v) (x : BitVec w) : (cast h x).getMsbD i = x.getMsbD i := by
  subst h; simp

@[simp] theorem getElem_cast (h : w = v) (x : BitVec w) (p : i < v) : (cast h x)[i] = x[i] := by
  subst h; simp

@[simp] theorem msb_cast (h : w = v) (x : BitVec w) : (cast h x).msb = x.msb := by
  simp [BitVec.msb]

/-! ### toInt/ofInt -/

/-- Prove equality of bitvectors in terms of nat operations. -/
theorem toInt_eq_toNat_cond (x : BitVec n) :
    x.toInt =
      if 2*x.toNat < 2^n then
        (x.toNat : Int)
      else
        (x.toNat : Int) - (2^n : Nat) :=
  rfl

theorem msb_eq_false_iff_two_mul_lt {x : BitVec w} : x.msb = false ↔ 2 * x.toNat < 2^w := by
  cases w <;> simp [Nat.pow_succ, Nat.mul_comm _ 2, msb_eq_decide, toNat_of_zero_length]

theorem msb_eq_true_iff_two_mul_ge {x : BitVec w} : x.msb = true ↔ 2 * x.toNat ≥ 2^w := by
  simp [← Bool.ne_false_iff, msb_eq_false_iff_two_mul_lt]

/-- Characterize `x.toInt` in terms of `x.msb`. -/
theorem toInt_eq_msb_cond (x : BitVec w) :
    x.toInt = if x.msb then (x.toNat : Int) - (2^w : Nat) else (x.toNat : Int) := by
  simp only [BitVec.toInt, ← msb_eq_false_iff_two_mul_lt]
  cases x.msb <;> rfl


theorem toInt_eq_toNat_bmod (x : BitVec n) : x.toInt = Int.bmod x.toNat (2^n) := by
  simp only [toInt_eq_toNat_cond]
  split
  next g =>
    rw [Int.bmod_pos] <;> simp only [←Int.ofNat_emod, toNat_mod_cancel]
    omega
  next g =>
    rw [Int.bmod_neg] <;> simp only [←Int.ofNat_emod, toNat_mod_cancel]
    omega

/-- Prove equality of bitvectors in terms of nat operations. -/
theorem eq_of_toInt_eq {x y : BitVec n} : x.toInt = y.toInt → x = y := by
  intro eq
  simp only [toInt_eq_toNat_cond] at eq
  apply eq_of_toNat_eq
  revert eq
  have _xlt := x.isLt
  have _ylt := y.isLt
  split <;> split <;> omega

theorem toInt_inj {x y : BitVec n} : x.toInt = y.toInt ↔ x = y :=
  Iff.intro eq_of_toInt_eq (congrArg BitVec.toInt)

theorem toInt_ne {x y : BitVec n} : x.toInt ≠ y.toInt ↔ x ≠ y  := by
  rw [Ne, toInt_inj]

@[simp, bv_toNat] theorem toNat_ofInt {n : Nat} (i : Int) :
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

@[simp] theorem ofInt_natCast (w n : Nat) :
  BitVec.ofInt w (n : Int) = BitVec.ofNat w n := rfl

@[simp] theorem ofInt_ofNat (w n : Nat) :
  BitVec.ofInt w (no_index (OfNat.ofNat n)) = BitVec.ofNat w (OfNat.ofNat n) := rfl

theorem toInt_neg_iff {w : Nat} {x : BitVec w} :
    BitVec.toInt x < 0 ↔ 2 ^ w ≤ 2 * x.toNat := by
  simp [toInt_eq_toNat_cond]; omega

theorem toInt_pos_iff {w : Nat} {x : BitVec w} :
    0 ≤ BitVec.toInt x ↔ 2 * x.toNat < 2 ^ w := by
  simp [toInt_eq_toNat_cond]; omega

theorem eq_zero_or_eq_one (a : BitVec 1) : a = 0#1 ∨ a = 1#1 := by
  obtain ⟨a, ha⟩ := a
  simp only [Nat.reducePow]
  have acases : a = 0 ∨ a = 1 := by omega
  rcases acases with ⟨rfl | rfl⟩
  · simp
  · case inr h =>
    subst h
    simp

@[simp]
theorem toInt_zero {w : Nat} : (0#w).toInt = 0 := by
  simp [BitVec.toInt, show 0 < 2^w by exact Nat.two_pow_pos w]

/-! ### slt -/

/--
A bitvector, when interpreted as an integer, is less than zero iff
its most significant bit is true.
-/
theorem slt_zero_iff_msb_cond (x : BitVec w) : x.slt 0#w ↔ x.msb = true := by
  have := toInt_eq_msb_cond x
  constructor
  · intros h
    apply Classical.byContradiction
    intros hmsb
    simp only [Bool.not_eq_true] at hmsb
    simp only [hmsb, Bool.false_eq_true, ↓reduceIte] at this
    simp only [BitVec.slt, toInt_zero, decide_eq_true_eq] at h
    omega /- Can't have `x.toInt` which is equal to `x.toNat` be strictly less than zero -/
  · intros h
    simp only [h, ↓reduceIte] at this
    simp [BitVec.slt, this]
    omega

/-! ### setWidth, zeroExtend and truncate -/

@[simp]
theorem truncate_eq_setWidth {v : Nat} {x : BitVec w} :
  truncate v x = setWidth v x := rfl

@[simp]
theorem zeroExtend_eq_setWidth {v : Nat} {x : BitVec w} :
  zeroExtend v x = setWidth v x := rfl

@[simp, bv_toNat] theorem toNat_setWidth' {m n : Nat} (p : m ≤ n) (x : BitVec m) :
    (setWidth' p x).toNat = x.toNat := by
  simp [setWidth']

@[simp, bv_toNat] theorem toNat_setWidth (i : Nat) (x : BitVec n) :
    BitVec.toNat (setWidth i x) = x.toNat % 2^i := by
  let ⟨x, lt_n⟩ := x
  simp only [setWidth]
  if n_le_i : n ≤ i then
    have x_lt_two_i : x < 2 ^ i := lt_two_pow_of_le lt_n n_le_i
    simp [n_le_i, Nat.mod_eq_of_lt, x_lt_two_i]
  else
    simp [n_le_i, toNat_ofNat]

theorem setWidth'_eq {x : BitVec w} (h : w ≤ v) : x.setWidth' h = x.setWidth v := by
  apply eq_of_toNat_eq
  rw [toNat_setWidth, toNat_setWidth']
  rw [Nat.mod_eq_of_lt]
  exact Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (Nat.zero_lt_two) h)

@[simp] theorem setWidth_eq (x : BitVec n) : setWidth n x = x := by
  apply eq_of_toNat_eq
  let ⟨x, lt_n⟩ := x
  simp [setWidth]

@[simp] theorem setWidth_zero (m n : Nat) : setWidth m 0#n = 0#m := by
  apply eq_of_toNat_eq
  simp [toNat_setWidth]

@[simp] theorem ofNat_toNat (m : Nat) (x : BitVec n) : BitVec.ofNat m x.toNat = setWidth m x := by
  apply eq_of_toNat_eq
  simp

/-- Moves one-sided left toNat equality to BitVec equality. -/
theorem toNat_eq_nat {x : BitVec w} {y : Nat}
  : (x.toNat = y) ↔ (y < 2^w ∧ (x = BitVec.ofNat w y)) := by
  apply Iff.intro
  · intro eq
    simp [←eq, x.isLt]
  · intro eq
    simp [Nat.mod_eq_of_lt, eq]

/-- Moves one-sided right toNat equality to BitVec equality. -/
theorem nat_eq_toNat {x : BitVec w} {y : Nat}
  : (y = x.toNat) ↔ (y < 2^w ∧ (x = BitVec.ofNat w y)) := by
  rw [@eq_comm _ _ x.toNat]
  apply toNat_eq_nat

theorem getElem_setWidth' (x : BitVec w) (i : Nat) (h : w ≤ v) (hi : i < v) :
    (setWidth' h x)[i] = x.getLsbD i := by
  rw [getElem_eq_testBit_toNat, toNat_setWidth', getLsbD]

@[simp]
theorem getElem_setWidth (m : Nat) (x : BitVec n) (i : Nat) (h : i < m) :
    (setWidth m x)[i] = x.getLsbD i := by
  rw [setWidth]
  split
  · rw [getElem_setWidth']
  · simp [getElem_eq_testBit_toNat, getLsbD]
    omega

theorem getElem?_setWidth' (x : BitVec w) (i : Nat) (h : w ≤ v) :
    (setWidth' h x)[i]? = if i < v then some (x.getLsbD i) else none := by
  simp [getElem?_eq, getElem_setWidth']

theorem getElem?_setWidth (m : Nat) (x : BitVec n) (i : Nat) :
    (x.setWidth m)[i]? = if i < m then some (x.getLsbD i) else none := by
  simp [getElem?_eq, getElem_setWidth]

@[simp] theorem getLsbD_setWidth' (ge : m ≥ n) (x : BitVec n) (i : Nat) :
    getLsbD (setWidth' ge x) i = getLsbD x i := by
  simp [getLsbD, toNat_setWidth']

@[simp] theorem getMsbD_setWidth' (ge : m ≥ n) (x : BitVec n) (i : Nat) :
    getMsbD (setWidth' ge x) i = (decide (i ≥ m - n) && getMsbD x (i - (m - n))) := by
  simp only [getMsbD, getLsbD_setWidth', gt_iff_lt]
  by_cases h₁ : decide (i < m) <;> by_cases h₂ : decide (i ≥ m - n) <;> by_cases h₃ : decide (i - (m - n) < n) <;>
    by_cases h₄ : n - 1 - (i - (m - n)) = m - 1 - i
  all_goals
    simp only [h₁, h₂, h₃, h₄]
    simp_all only [ge_iff_le, decide_eq_true_eq, Nat.not_le, Nat.not_lt, Bool.true_and,
      Bool.false_and, Bool.and_self] <;>
    (try apply getLsbD_ge) <;>
    (try apply (getLsbD_ge _ _ _).symm) <;>
    omega

@[simp] theorem getLsbD_setWidth (m : Nat) (x : BitVec n) (i : Nat) :
    getLsbD (setWidth m x) i = (decide (i < m) && getLsbD x i) := by
  simp [getLsbD, toNat_setWidth, Nat.testBit_mod_two_pow]

@[simp] theorem getMsbD_setWidth_add {x : BitVec w} (h : k ≤ i) :
    (x.setWidth (w + k)).getMsbD i = x.getMsbD (i - k) := by
  by_cases h : w = 0
  · subst h; simp [of_length_zero]
  simp only [getMsbD, getLsbD_setWidth]
  by_cases h₁ : i < w + k <;> by_cases h₂ : i - k < w <;> by_cases h₃ : w + k - 1 - i < w + k
    <;> simp [h₁, h₂, h₃]
  · congr 1
    omega
  all_goals (first | apply getLsbD_ge | apply Eq.symm; apply getLsbD_ge)
    <;> omega

@[simp] theorem cast_setWidth (h : v = v') (x : BitVec w) :
    cast h (setWidth v x) = setWidth v' x := by
  subst h
  ext
  simp

@[simp] theorem setWidth_setWidth_of_le (x : BitVec w) (h : k ≤ l) :
    (x.setWidth l).setWidth k = x.setWidth k := by
  ext i
  simp only [getLsbD_setWidth, Fin.is_lt, decide_true, Bool.true_and]
  have p := lt_of_getLsbD (x := x) (i := i)
  revert p
  cases getLsbD x i <;> simp; omega

@[simp] theorem setWidth_cast {h : w = v} : (cast h x).setWidth k = x.setWidth k := by
  apply eq_of_getLsbD_eq
  simp

theorem msb_setWidth (x : BitVec w) : (x.setWidth v).msb = (decide (0 < v) && x.getLsbD (v - 1)) := by
  rw [msb_eq_getLsbD_last]
  simp only [getLsbD_setWidth]
  cases getLsbD x (v - 1) <;> simp; omega

theorem msb_setWidth' (x : BitVec w) (h : w ≤ v) : (x.setWidth' h).msb = (decide (0 < v) && x.getLsbD (v - 1)) := by
  rw [setWidth'_eq, msb_setWidth]

theorem msb_setWidth'' (x : BitVec w) : (x.setWidth (k + 1)).msb = x.getLsbD k := by
  simp [BitVec.msb, getMsbD]

/-- zero extending a bitvector to width 1 equals the boolean of the lsb. -/
theorem setWidth_one_eq_ofBool_getLsb_zero (x : BitVec w) :
    x.setWidth 1 = BitVec.ofBool (x.getLsbD 0) := by
  ext i
  simp [getLsbD_setWidth, Fin.fin_one_eq_zero i]

/-- Zero extending `1#v` to `1#w` equals `1#w` when `v > 0`. -/
theorem setWidth_ofNat_one_eq_ofNat_one_of_lt {v w : Nat} (hv : 0 < v) :
    (BitVec.ofNat v 1).setWidth w = BitVec.ofNat w 1 := by
  ext ⟨i, hilt⟩
  simp only [getLsbD_setWidth, hilt, decide_true, getLsbD_ofNat, Bool.true_and,
    Bool.and_iff_right_iff_imp, decide_eq_true_eq]
  intros hi₁
  have hv := Nat.testBit_one_eq_true_iff_self_eq_zero.mp hi₁
  omega

/-- Truncating to width 1 produces a bitvector equal to the least significant bit. -/
theorem setWidth_one {x : BitVec w} :
    x.setWidth 1 = ofBool (x.getLsbD 0) := by
  ext i
  simp [show i = 0 by omega]

@[simp] theorem setWidth_ofNat_of_le (h : v ≤ w) (x : Nat) : setWidth v (BitVec.ofNat w x) = BitVec.ofNat v x := by
  apply BitVec.eq_of_toNat_eq
  simp only [toNat_setWidth, toNat_ofNat]
  rw [Nat.mod_mod_of_dvd]
  exact Nat.pow_dvd_pow_iff_le_right'.mpr h

/-! ## extractLsb -/

@[simp]
protected theorem extractLsb_ofFin {n} (x : Fin (2^n)) (hi lo : Nat) :
  extractLsb hi lo (@BitVec.ofFin n x) = .ofNat (hi-lo+1) (x.val >>> lo) := rfl

@[simp]
protected theorem extractLsb_ofNat (x n : Nat) (hi lo : Nat) :
  extractLsb hi lo (BitVec.ofNat n x) = .ofNat (hi - lo + 1) ((x % 2^n) >>> lo) := by
  apply eq_of_getLsbD_eq
  intro ⟨i, _lt⟩
  simp [BitVec.ofNat]

@[simp] theorem extractLsb'_toNat (s m : Nat) (x : BitVec n) :
  (extractLsb' s m x).toNat = (x.toNat >>> s) % 2^m := rfl

@[simp] theorem extractLsb_toNat (hi lo : Nat) (x : BitVec n) :
  (extractLsb hi lo x).toNat = (x.toNat >>> lo) % 2^(hi-lo+1) := rfl

@[simp] theorem getElem_extractLsb' {start len : Nat} {x : BitVec n} {i : Nat} (h : i < len) :
    (extractLsb' start len x)[i] = x.getLsbD (start+i) := by
  simp [getElem_eq_testBit_toNat, getLsbD, h]

@[simp] theorem getLsbD_extractLsb' (start len : Nat) (x : BitVec n) (i : Nat) :
    (extractLsb' start len x).getLsbD i = (i < len && x.getLsbD (start+i)) := by
  simp [getLsbD, Nat.lt_succ]

@[simp] theorem getElem_extract {hi lo : Nat} {x : BitVec n} {i : Nat} (h : i < hi - lo + 1) :
    (extractLsb hi lo x)[i] = getLsbD x (lo+i) := by
  simp [getElem_eq_testBit_toNat, getLsbD, h]

@[simp] theorem getLsbD_extract (hi lo : Nat) (x : BitVec n) (i : Nat) :
    getLsbD (extractLsb hi lo x) i = (i ≤ (hi-lo) && getLsbD x (lo+i)) := by
  simp [getLsbD, Nat.lt_succ]

theorem extractLsb'_eq_extractLsb {w : Nat} (x : BitVec w) (start len : Nat) (h : len > 0) :
    x.extractLsb' start len = (x.extractLsb (len - 1 + start) start).cast (by omega) := by
  apply eq_of_toNat_eq
  simp [extractLsb, show len - 1 + 1 = len by omega]

/-! ### allOnes -/

@[simp] theorem toNat_allOnes : (allOnes v).toNat = 2^v - 1 := by
  unfold allOnes
  simp

@[simp] theorem getLsbD_allOnes : (allOnes v).getLsbD i = decide (i < v) := by
  simp [allOnes]

@[simp] theorem getElem_allOnes (i : Nat) (h : i < v) : (allOnes v)[i] = true := by
  simp [getElem_eq_testBit_toNat, h]

@[simp] theorem ofFin_add_rev (x : Fin (2^n)) : ofFin (x + x.rev) = allOnes n := by
  ext
  simp only [Fin.rev, getLsbD_ofFin, getLsbD_allOnes, Fin.is_lt, decide_true]
  rw [Fin.add_def]
  simp only [Nat.testBit_mod_two_pow, Fin.is_lt, decide_true, Bool.true_and]
  have h : (x : Nat) + (2 ^ n - (x + 1)) = 2 ^ n - 1 := by omega
  rw [h, Nat.testBit_two_pow_sub_one]
  simp

/-! ### or -/

@[simp] theorem toNat_or (x y : BitVec v) :
    BitVec.toNat (x ||| y) = BitVec.toNat x ||| BitVec.toNat y := rfl

@[simp] theorem toFin_or (x y : BitVec v) :
    BitVec.toFin (x ||| y) = BitVec.toFin x ||| BitVec.toFin y := by
  apply Fin.eq_of_val_eq
  exact (Nat.mod_eq_of_lt <| Nat.or_lt_two_pow x.isLt y.isLt).symm

@[simp] theorem getLsbD_or {x y : BitVec v} : (x ||| y).getLsbD i = (x.getLsbD i || y.getLsbD i) := by
  rw [← testBit_toNat, getLsbD, getLsbD]
  simp

@[simp] theorem getMsbD_or {x y : BitVec w} : (x ||| y).getMsbD i = (x.getMsbD i || y.getMsbD i) := by
  simp only [getMsbD]
  by_cases h : i < w <;> simp [h]

@[simp] theorem getElem_or {x y : BitVec w} {i : Nat} (h : i < w) : (x ||| y)[i] = (x[i] || y[i]) := by
  simp [getElem_eq_testBit_toNat]

@[simp] theorem msb_or {x y : BitVec w} : (x ||| y).msb = (x.msb || y.msb) := by
  simp [BitVec.msb]

@[simp] theorem setWidth_or {x y : BitVec w} :
    (x ||| y).setWidth k = x.setWidth k ||| y.setWidth k := by
  ext
  simp

theorem or_assoc (x y z : BitVec w) :
    x ||| y ||| z = x ||| (y ||| z) := by
  ext i
  simp [Bool.or_assoc]
instance : Std.Associative (α := BitVec n) (· ||| ·) := ⟨BitVec.or_assoc⟩

theorem or_comm (x y : BitVec w) :
    x ||| y = y ||| x := by
  ext i
  simp [Bool.or_comm]
instance : Std.Commutative (fun (x y : BitVec w) => x ||| y) := ⟨BitVec.or_comm⟩

@[simp] theorem or_self {x : BitVec w} : x ||| x = x := by
  ext i
  simp

instance : Std.IdempotentOp (α := BitVec n) (· ||| · ) where
  idempotent _ := BitVec.or_self

@[simp] theorem or_zero {x : BitVec w} : x ||| 0#w = x := by
  ext i
  simp

instance : Std.LawfulCommIdentity (α := BitVec n) (· ||| · ) (0#n) where
  right_id _ := BitVec.or_zero

@[simp] theorem zero_or {x : BitVec w} : 0#w ||| x = x := by
  ext i
  simp

@[simp] theorem or_allOnes {x : BitVec w} : x ||| allOnes w = allOnes w := by
  ext i
  simp

@[simp] theorem allOnes_or {x : BitVec w} : allOnes w ||| x = allOnes w := by
  ext i
  simp

/-! ### and -/

@[simp] theorem toNat_and (x y : BitVec v) :
    BitVec.toNat (x &&& y) = BitVec.toNat x &&& BitVec.toNat y := rfl

@[simp] theorem toFin_and (x y : BitVec v) :
    BitVec.toFin (x &&& y) = BitVec.toFin x &&& BitVec.toFin y := by
  apply Fin.eq_of_val_eq
  exact (Nat.mod_eq_of_lt <| Nat.and_lt_two_pow _ y.isLt).symm

@[simp] theorem getLsbD_and {x y : BitVec v} : (x &&& y).getLsbD i = (x.getLsbD i && y.getLsbD i) := by
  rw [← testBit_toNat, getLsbD, getLsbD]
  simp

@[simp] theorem getMsbD_and {x y : BitVec w} : (x &&& y).getMsbD i = (x.getMsbD i && y.getMsbD i) := by
  simp only [getMsbD]
  by_cases h : i < w <;> simp [h]

@[simp] theorem getElem_and {x y : BitVec w} {i : Nat} (h : i < w) : (x &&& y)[i] = (x[i] && y[i]) := by
  simp [getElem_eq_testBit_toNat]

@[simp] theorem msb_and {x y : BitVec w} : (x &&& y).msb = (x.msb && y.msb) := by
  simp [BitVec.msb]

@[simp] theorem setWidth_and {x y : BitVec w} :
    (x &&& y).setWidth k = x.setWidth k &&& y.setWidth k := by
  ext
  simp

theorem and_assoc (x y z : BitVec w) :
    x &&& y &&& z = x &&& (y &&& z) := by
  ext i
  simp [Bool.and_assoc]
instance : Std.Associative (α := BitVec n) (· &&& ·) := ⟨BitVec.and_assoc⟩

theorem and_comm (x y : BitVec w) :
    x &&& y = y &&& x := by
  ext i
  simp [Bool.and_comm]
instance : Std.Commutative (fun (x y : BitVec w) => x &&& y) := ⟨BitVec.and_comm⟩

@[simp] theorem and_self {x : BitVec w} : x &&& x = x := by
  ext i
  simp

instance : Std.IdempotentOp (α := BitVec n) (· &&& · ) where
  idempotent _ := BitVec.and_self

@[simp] theorem and_zero {x : BitVec w} : x &&& 0#w = 0#w := by
  ext i
  simp

@[simp] theorem zero_and {x : BitVec w} : 0#w &&& x = 0#w := by
  ext i
  simp

@[simp] theorem and_allOnes {x : BitVec w} : x &&& allOnes w = x := by
  ext i
  simp

instance : Std.LawfulCommIdentity (α := BitVec n) (· &&& · ) (allOnes n) where
  right_id _ := BitVec.and_allOnes

@[simp] theorem allOnes_and {x : BitVec w} : allOnes w &&& x = x := by
  ext i
  simp

/-! ### xor -/

@[simp] theorem toNat_xor (x y : BitVec v) :
    BitVec.toNat (x ^^^ y) = BitVec.toNat x ^^^ BitVec.toNat y := rfl

@[simp] theorem toFin_xor (x y : BitVec v) :
    BitVec.toFin (x ^^^ y) = BitVec.toFin x ^^^ BitVec.toFin y := by
  apply Fin.eq_of_val_eq
  exact (Nat.mod_eq_of_lt <| Nat.xor_lt_two_pow x.isLt y.isLt).symm

@[simp] theorem getLsbD_xor {x y : BitVec v} :
    (x ^^^ y).getLsbD i = ((x.getLsbD i) ^^ (y.getLsbD i)) := by
  rw [← testBit_toNat, getLsbD, getLsbD]
  simp

@[simp] theorem getMsbD_xor {x y : BitVec w} :
    (x ^^^ y).getMsbD i = (x.getMsbD i ^^ y.getMsbD i) := by
  simp only [getMsbD]
  by_cases h : i < w <;> simp [h]

@[simp] theorem getElem_xor {x y : BitVec w} {i : Nat} (h : i < w) : (x ^^^ y)[i] = (x[i] ^^ y[i]) := by
  simp [getElem_eq_testBit_toNat]

@[simp] theorem msb_xor {x y : BitVec w} :
    (x ^^^ y).msb = (x.msb ^^ y.msb) := by
  simp [BitVec.msb]

@[simp] theorem setWidth_xor {x y : BitVec w} :
    (x ^^^ y).setWidth k = x.setWidth k ^^^ y.setWidth k := by
  ext
  simp

theorem xor_assoc (x y z : BitVec w) :
    x ^^^ y ^^^ z = x ^^^ (y ^^^ z) := by
  ext i
  simp [Bool.xor_assoc]
instance : Std.Associative (fun (x y : BitVec w) => x ^^^ y) := ⟨BitVec.xor_assoc⟩

theorem xor_comm (x y : BitVec w) :
    x ^^^ y = y ^^^ x := by
  ext i
  simp [Bool.xor_comm]
instance : Std.Commutative (fun (x y : BitVec w) => x ^^^ y) := ⟨BitVec.xor_comm⟩

@[simp] theorem xor_self {x : BitVec w} : x ^^^ x = 0#w := by
  ext i
  simp

@[simp] theorem xor_zero {x : BitVec w} : x ^^^ 0#w = x := by
  ext i
  simp

instance : Std.LawfulCommIdentity (α := BitVec n) (· ^^^ · ) (0#n) where
  right_id _ := BitVec.xor_zero

@[simp] theorem zero_xor {x : BitVec w} : 0#w ^^^ x = x := by
  ext i
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
      · simp only [decide_eq_false_iff_not, Nat.not_lt] at w
        simp only [Bool.false_bne, Bool.false_and]
        rw [Nat.testBit_lt_two_pow]
        calc BitVec.toNat x < 2 ^ v := isLt _
          _ ≤ 2 ^ i := Nat.pow_le_pow_of_le_right Nat.zero_lt_two w
      · simp

@[simp] theorem ofInt_negSucc_eq_not_ofNat {w n : Nat} :
    BitVec.ofInt w (Int.negSucc n) = ~~~.ofNat w n := by
  simp only [BitVec.ofInt, Int.toNat, Int.ofNat_eq_coe, toNat_eq, toNat_ofNatLt, toNat_not,
    toNat_ofNat]
  cases h : Int.negSucc n % ((2 ^ w : Nat) : Int)
  case ofNat =>
    rw [Int.ofNat_eq_coe, Int.negSucc_emod] at h
    · dsimp only
      omega
    · omega
  case negSucc a =>
    have neg := Int.negSucc_lt_zero a
    have _ : 0 ≤ Int.negSucc n % ((2 ^ w : Nat) : Int) := Int.emod_nonneg _ (by omega)
    omega

@[simp] theorem toFin_not (x : BitVec w) :
    (~~~x).toFin = x.toFin.rev := by
  apply Fin.val_inj.mp
  simp only [val_toFin, toNat_not, Fin.val_rev]
  omega

@[simp] theorem getLsbD_not {x : BitVec v} : (~~~x).getLsbD i = (decide (i < v) && ! x.getLsbD i) := by
  by_cases h' : i < v <;> simp_all [not_def]

@[simp] theorem getElem_not {x : BitVec w} {i : Nat} (h : i < w) : (~~~x)[i] = !x[i] := by
  simp only [getElem_eq_testBit_toNat, toNat_not]
  rw [← Nat.sub_add_eq, Nat.add_comm 1]
  rw [Nat.testBit_two_pow_sub_succ x.isLt]
  simp [h]

@[simp] theorem setWidth_not {x : BitVec w} (h : k ≤ w) :
    (~~~x).setWidth k = ~~~(x.setWidth k) := by
  ext
  simp [h]
  omega

@[simp] theorem not_zero : ~~~(0#n) = allOnes n := by
  ext
  simp

@[simp] theorem not_allOnes : ~~~ allOnes w = 0#w := by
  ext
  simp

@[simp] theorem xor_allOnes {x : BitVec w} : x ^^^ allOnes w = ~~~ x := by
  ext i
  simp

@[simp] theorem allOnes_xor {x : BitVec w} : allOnes w ^^^ x = ~~~ x := by
  ext i
  simp

@[simp]
theorem not_not {b : BitVec w} : ~~~(~~~b) = b := by
  ext i
  simp

theorem not_eq_comm {x y : BitVec w} : ~~~ x = y ↔ x = ~~~ y := by
  constructor
  · intro h
    rw [← h]
    simp
  · intro h
    rw [h]
    simp

@[simp] theorem getMsb_not {x : BitVec w} :
    (~~~x).getMsbD i = (decide (i < w) && !(x.getMsbD i)) := by
  simp only [getMsbD]
  by_cases h : i < w
  · simp [h]; omega
  · simp [h];

@[simp] theorem msb_not {x : BitVec w} : (~~~x).msb = (decide (0 < w) && !x.msb) := by
  simp [BitVec.msb]

/-! ### cast -/

@[simp] theorem not_cast {x : BitVec w} (h : w = w') : ~~~(cast h x) = cast h (~~~x) := by
  ext
  simp_all [lt_of_getLsbD]

@[simp] theorem and_cast {x y : BitVec w} (h : w = w') : cast h x &&& cast h y = cast h (x &&& y) := by
  ext
  simp_all [lt_of_getLsbD]

@[simp] theorem or_cast {x y : BitVec w} (h : w = w') : cast h x ||| cast h y = cast h (x ||| y) := by
  ext
  simp_all [lt_of_getLsbD]

@[simp] theorem xor_cast {x y : BitVec w} (h : w = w') : cast h x ^^^ cast h y = cast h (x ^^^ y) := by
  ext
  simp_all [lt_of_getLsbD]

/-! ### shiftLeft -/

@[simp, bv_toNat] theorem toNat_shiftLeft {x : BitVec v} :
    BitVec.toNat (x <<< n) = BitVec.toNat x <<< n % 2^v :=
  BitVec.toNat_ofNat _ _

@[simp] theorem toFin_shiftLeft {n : Nat} (x : BitVec w) :
    BitVec.toFin (x <<< n) = Fin.ofNat' (2^w) (x.toNat <<< n) := rfl

@[simp]
theorem shiftLeft_zero (x : BitVec w) : x <<< 0 = x := by
  apply eq_of_toNat_eq
  simp

@[simp]
theorem zero_shiftLeft (n : Nat) : 0#w <<< n = 0#w := by
  simp [bv_toNat]

@[simp] theorem getLsbD_shiftLeft (x : BitVec m) (n) :
    getLsbD (x <<< n) i = (decide (i < m) && !decide (i < n) && getLsbD x (i - n)) := by
  rw [← testBit_toNat, getLsbD]
  simp only [toNat_shiftLeft, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft, ge_iff_le]
  -- This step could be a case bashing tactic.
  cases h₁ : decide (i < m) <;> cases h₂ : decide (n ≤ i) <;> cases h₃ : decide (i < n)
  all_goals { simp_all <;> omega }

@[simp] theorem getElem_shiftLeft {x : BitVec m} {n : Nat} (h : i < m) :
    (x <<< n)[i] = (!decide (i < n) && getLsbD x (i - n)) := by
  rw [← testBit_toNat, getElem_eq_testBit_toNat]
  simp only [toNat_shiftLeft, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft, ge_iff_le]
  -- This step could be a case bashing tactic.
  cases h₁ : decide (i < m) <;> cases h₂ : decide (n ≤ i) <;> cases h₃ : decide (i < n)
  all_goals { simp_all <;> omega }

theorem shiftLeft_xor_distrib (x y : BitVec w) (n : Nat) :
    (x ^^^ y) <<< n = (x <<< n) ^^^ (y <<< n) := by
  ext i
  simp only [getLsbD_shiftLeft, Fin.is_lt, decide_true, Bool.true_and, getLsbD_xor]
  by_cases h : i < n
    <;> simp [h]

theorem shiftLeft_and_distrib (x y : BitVec w) (n : Nat) :
    (x &&& y) <<< n = (x <<< n) &&& (y <<< n) := by
  ext i
  simp only [getLsbD_shiftLeft, Fin.is_lt, decide_true, Bool.true_and, getLsbD_and]
  by_cases h : i < n
    <;> simp [h]

theorem shiftLeft_or_distrib (x y : BitVec w) (n : Nat) :
    (x ||| y) <<< n = (x <<< n) ||| (y <<< n) := by
  ext i
  simp only [getLsbD_shiftLeft, Fin.is_lt, decide_true, Bool.true_and, getLsbD_or]
  by_cases h : i < n
    <;> simp [h]

@[simp] theorem getMsbD_shiftLeft (x : BitVec w) (i) :
    (x <<< i).getMsbD k = x.getMsbD (k + i) := by
  simp only [getMsbD, getLsbD_shiftLeft]
  by_cases h : w = 0
  · subst h; simp
  have t : w - 1 - k < w := by omega
  simp only [t]
  simp only [decide_true, Nat.sub_sub, Bool.true_and, Nat.add_assoc]
  by_cases h₁ : k < w <;> by_cases h₂ : w - (1 + k) < i <;> by_cases h₃ : k + i < w
    <;> simp only [h₁, h₂, h₃, decide_false, h₂, decide_true, Bool.not_true, Bool.false_and, Bool.and_self,
      Bool.true_and, Bool.false_eq, Bool.false_and, Bool.not_false]
    <;> (first | apply getLsbD_ge | apply Eq.symm; apply getLsbD_ge)
    <;> omega

theorem shiftLeftZeroExtend_eq {x : BitVec w} :
    shiftLeftZeroExtend x n = setWidth (w+n) x <<< n := by
  apply eq_of_toNat_eq
  rw [shiftLeftZeroExtend, setWidth]
  split
  · simp
    rw [Nat.mod_eq_of_lt]
    rw [Nat.shiftLeft_eq, Nat.pow_add]
    exact Nat.mul_lt_mul_of_pos_right x.isLt (Nat.two_pow_pos _)
  · omega

@[simp] theorem getElem_shiftLeftZeroExtend {x : BitVec m} {n : Nat} (h : i < m + n) :
    (shiftLeftZeroExtend x n)[i] = ((! decide (i < n)) && getLsbD x (i - n)) := by
  rw [shiftLeftZeroExtend_eq, getLsbD]
  simp only [getElem_eq_testBit_toNat, getLsbD_shiftLeft, getLsbD_setWidth]
  cases h₁ : decide (i < n) <;> cases h₂ : decide (i - n < m + n)
    <;> simp_all [h]
    <;> omega

@[simp] theorem getLsbD_shiftLeftZeroExtend (x : BitVec m) (n : Nat) :
    getLsbD (shiftLeftZeroExtend x n) i = ((! decide (i < n)) && getLsbD x (i - n)) := by
  rw [shiftLeftZeroExtend_eq]
  simp only [getLsbD_shiftLeft, getLsbD_setWidth]
  cases h₁ : decide (i < n) <;> cases h₂ : decide (i - n < m + n) <;> cases h₃ : decide (i < m + n)
    <;> simp_all
    <;> (rw [getLsbD_ge]; omega)

@[simp] theorem getMsbD_shiftLeftZeroExtend (x : BitVec m) (n : Nat) :
    getMsbD (shiftLeftZeroExtend x n) i = getMsbD x i := by
  have : n ≤ i + n := by omega
  simp_all [shiftLeftZeroExtend_eq]

@[simp] theorem msb_shiftLeftZeroExtend (x : BitVec w) (i : Nat) :
    (shiftLeftZeroExtend x i).msb = x.msb := by
  simp [shiftLeftZeroExtend_eq, BitVec.msb]

theorem shiftLeft_add {w : Nat} (x : BitVec w) (n m : Nat) :
    x <<< (n + m) = (x <<< n) <<< m := by
  ext i
  simp only [getLsbD_shiftLeft, Fin.is_lt, decide_true, Bool.true_and]
  rw [show i - (n + m) = (i - m - n) by omega]
  cases h₂ : decide (i < m) <;>
  cases h₃ : decide (i - m < w) <;>
  cases h₄ : decide (i - m < n) <;>
  cases h₅ : decide (i < n + m) <;>
    simp at * <;> omega

@[simp]
theorem allOnes_shiftLeft_and_shiftLeft {x : BitVec w} {n : Nat} :
    BitVec.allOnes w <<< n &&& x <<< n = x <<< n := by
  simp [← BitVec.shiftLeft_and_distrib]

@[simp]
theorem allOnes_shiftLeft_or_shiftLeft {x : BitVec w} {n : Nat} :
    BitVec.allOnes w <<< n ||| x <<< n = BitVec.allOnes w <<< n := by
  simp [← shiftLeft_or_distrib]

@[deprecated shiftLeft_add (since := "2024-06-02")]
theorem shiftLeft_shiftLeft {w : Nat} (x : BitVec w) (n m : Nat) :
    (x <<< n) <<< m = x <<< (n + m) := by
  rw [shiftLeft_add]

/-! ### shiftLeft reductions from BitVec to Nat -/

@[simp]
theorem shiftLeft_eq' {x : BitVec w₁} {y : BitVec w₂} : x <<< y = x <<< y.toNat := by rfl

theorem shiftLeft_zero' {x : BitVec w₁} : x <<< 0#w₂ = x := by simp

theorem shiftLeft_shiftLeft' {x : BitVec w₁} {y : BitVec w₂} {z : BitVec w₃} :
    x <<< y <<< z = x <<< (y.toNat + z.toNat) := by
  simp [shiftLeft_add]

theorem getLsbD_shiftLeft' {x : BitVec w₁} {y : BitVec w₂} {i : Nat} :
    (x <<< y).getLsbD i = (decide (i < w₁) && !decide (i < y.toNat) && x.getLsbD (i - y.toNat)) := by
  simp [shiftLeft_eq', getLsbD_shiftLeft]

@[simp]
theorem getElem_shiftLeft' {x : BitVec w₁} {y : BitVec w₂} {i : Nat} (h : i < w₁) :
    (x <<< y)[i] = (!decide (i < y.toNat) && x.getLsbD (i - y.toNat)) := by
  simp [shiftLeft_eq', getLsbD_shiftLeft]

/-! ### ushiftRight -/

@[simp, bv_toNat] theorem toNat_ushiftRight (x : BitVec n) (i : Nat) :
    (x >>> i).toNat = x.toNat >>> i := rfl

@[simp] theorem getLsbD_ushiftRight (x : BitVec n) (i j : Nat) :
    getLsbD (x >>> i) j = getLsbD x (i+j) := by
  unfold getLsbD ; simp

@[simp] theorem getElem_ushiftRight (x : BitVec w) (i n : Nat) (h : i < w) :
    (x >>> n)[i] = x.getLsbD (n + i) := by
  simp [getElem_eq_testBit_toNat, toNat_ushiftRight, Nat.testBit_shiftRight, getLsbD]

theorem ushiftRight_xor_distrib (x y : BitVec w) (n : Nat) :
    (x ^^^ y) >>> n = (x >>> n) ^^^ (y >>> n) := by
  ext
  simp

theorem ushiftRight_and_distrib (x y : BitVec w) (n : Nat) :
    (x &&& y) >>> n = (x >>> n) &&& (y >>> n) := by
  ext
  simp

theorem ushiftRight_or_distrib (x y : BitVec w)  (n : Nat) :
    (x ||| y) >>> n = (x >>> n) ||| (y >>> n) := by
  ext
  simp

@[simp]
theorem ushiftRight_zero (x : BitVec w) : x >>> 0 = x := by
  simp [bv_toNat]

@[simp]
theorem zero_ushiftRight {n : Nat} : 0#w >>> n = 0#w := by
  simp [bv_toNat]

/--
Shifting right by `n < w` yields a bitvector whose value is less than `2 ^ (w - n)`.
-/
theorem toNat_ushiftRight_lt (x : BitVec w) (n : Nat) (hn : n ≤ w) :
    (x >>> n).toNat < 2 ^ (w - n) := by
  rw [toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul]
  · rw [Nat.pow_sub_mul_pow]
    · apply x.isLt
    · apply hn
  · apply Nat.pow_pos (by decide)

@[simp]
theorem getMsbD_ushiftRight {x : BitVec w} {i n : Nat} :
    (x >>> n).getMsbD i = (decide (i < w) && (!decide (i < n) && x.getMsbD (i - n))) := by
  simp only [getMsbD, getLsbD_ushiftRight]
  by_cases h : i < n
  · simp [getLsbD_ge, show w ≤ (n + (w - 1 - i)) by omega]
    omega
  · by_cases h₁ : i < w
    · simp only [h, decide_false, Bool.not_false, show i - n < w by omega, decide_true,
        Bool.true_and]
      congr
      omega
    · simp [h, h₁]

@[simp]
theorem msb_ushiftRight {x : BitVec w} {n : Nat} :
    (x >>> n).msb = (!decide (0 < n) && x.msb) := by
  induction n
  case zero =>
    simp
  case succ nn ih =>
    simp [BitVec.ushiftRight_eq, getMsbD_ushiftRight, BitVec.msb, ih, show nn + 1 > 0 by omega]

/-! ### ushiftRight reductions from BitVec to Nat -/

@[simp]
theorem ushiftRight_eq' (x : BitVec w₁) (y : BitVec w₂) :
    x >>> y = x >>> y.toNat := by rfl

/-! ### sshiftRight -/

theorem sshiftRight_eq {x : BitVec n} {i : Nat} :
    x.sshiftRight i = BitVec.ofInt n (x.toInt >>> i) := by
  apply BitVec.eq_of_toInt_eq
  simp [BitVec.sshiftRight]

/-- if the msb is false, the arithmetic shift right equals logical shift right -/
theorem sshiftRight_eq_of_msb_false {x : BitVec w} {s : Nat} (h : x.msb = false) :
    (x.sshiftRight s) = x >>> s := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.sshiftRight_eq, BitVec.toInt_eq_toNat_cond]
  have hxbound : 2 * x.toNat < 2 ^ w := BitVec.msb_eq_false_iff_two_mul_lt.mp h
  simp only [hxbound, ↓reduceIte, Int.natCast_shiftRight, Int.ofNat_eq_coe, ofInt_natCast,
    toNat_ofNat, toNat_ushiftRight]
  replace hxbound : x.toNat >>> s < 2 ^ w := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.lt_of_le_of_lt (Nat.div_le_self ..) x.isLt
  apply Nat.mod_eq_of_lt hxbound

/--
If the msb is `true`, the arithmetic shift right equals negating,
then logical shifting right, then negating again.
The double negation preserves the lower bits that have been shifted,
and the outer negation ensures that the high bits are '1'. -/
theorem sshiftRight_eq_of_msb_true {x : BitVec w} {s : Nat} (h : x.msb = true) :
    (x.sshiftRight s) = ~~~((~~~x) >>> s) := by
  apply BitVec.eq_of_toNat_eq
  rcases w with rfl | w
  · simp [toNat_of_zero_length]
  · rw [BitVec.sshiftRight_eq, BitVec.toInt_eq_toNat_cond]
    have hxbound : (2 * x.toNat ≥ 2 ^ (w + 1)) := BitVec.msb_eq_true_iff_two_mul_ge.mp h
    replace hxbound : ¬ (2 * x.toNat < 2 ^ (w + 1)) := by omega
    simp only [hxbound, ↓reduceIte, toNat_ofInt, toNat_not, toNat_ushiftRight]
    rw [← Int.subNatNat_eq_coe, Int.subNatNat_of_lt (by omega),
        Nat.pred_eq_sub_one, Int.negSucc_shiftRight,
        Int.emod_negSucc, Int.natAbs_ofNat, Nat.succ_eq_add_one,
        Int.subNatNat_of_le (by omega), Int.toNat_ofNat, Nat.mod_eq_of_lt,
        Nat.sub_right_comm]
    omega
    · rw [Nat.shiftRight_eq_div_pow]
      apply Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)

theorem getLsbD_sshiftRight (x : BitVec w) (s i : Nat) :
    getLsbD (x.sshiftRight s) i =
      (!decide (w ≤ i) && if s + i < w then x.getLsbD (s + i) else x.msb) := by
  rcases hmsb : x.msb with rfl | rfl
  · simp only [sshiftRight_eq_of_msb_false hmsb, getLsbD_ushiftRight, Bool.if_false_right]
    by_cases hi : i ≥ w
    · simp only [hi, decide_true, Bool.not_true, Bool.false_and]
      apply getLsbD_ge
      omega
    · simp only [hi, decide_false, Bool.not_false, Bool.true_and, Bool.iff_and_self,
        decide_eq_true_eq]
      intros hlsb
      apply BitVec.lt_of_getLsbD hlsb
  · by_cases hi : i ≥ w
    · simp [hi]
    · simp only [sshiftRight_eq_of_msb_true hmsb, getLsbD_not, getLsbD_ushiftRight, Bool.not_and,
        Bool.not_not, hi, decide_false, Bool.not_false, Bool.if_true_right, Bool.true_and,
        Bool.and_iff_right_iff_imp, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        Nat.not_lt, decide_eq_true_eq]
      omega

theorem getElem_sshiftRight {x : BitVec w} {s i : Nat} (h : i < w) :
    (x.sshiftRight s)[i] = (if s + i < w then x.getLsbD (s + i) else x.msb) := by
  rcases hmsb : x.msb with rfl | rfl
  · simp only [sshiftRight_eq_of_msb_false hmsb, getElem_ushiftRight, Bool.if_false_right,
    Bool.iff_and_self, decide_eq_true_eq]
    intros hlsb
    apply BitVec.lt_of_getLsbD hlsb
  · simp [sshiftRight_eq_of_msb_true hmsb]

theorem sshiftRight_xor_distrib (x y : BitVec w) (n : Nat) :
    (x ^^^ y).sshiftRight n = (x.sshiftRight n) ^^^ (y.sshiftRight n) := by
  ext i
  simp only [getLsbD_sshiftRight, getLsbD_xor, msb_xor]
  split
    <;> by_cases w ≤ i
    <;> simp [*]

theorem sshiftRight_and_distrib (x y : BitVec w) (n : Nat) :
    (x &&& y).sshiftRight n = (x.sshiftRight n) &&& (y.sshiftRight n) := by
  ext i
  simp only [getLsbD_sshiftRight, getLsbD_and, msb_and]
  split
    <;> by_cases w ≤ i
    <;> simp [*]

theorem sshiftRight_or_distrib (x y : BitVec w) (n : Nat) :
    (x ||| y).sshiftRight n = (x.sshiftRight n) ||| (y.sshiftRight n) := by
  ext i
  simp only [getLsbD_sshiftRight, getLsbD_or, msb_or]
  split
    <;> by_cases w ≤ i
    <;> simp [*]

/-- The msb after arithmetic shifting right equals the original msb. -/
@[simp]
theorem msb_sshiftRight {n : Nat} {x : BitVec w} :
    (x.sshiftRight n).msb = x.msb := by
  rw [msb_eq_getLsbD_last, getLsbD_sshiftRight, msb_eq_getLsbD_last]
  by_cases hw₀ : w = 0
  · simp [hw₀]
  · simp only [show ¬(w ≤ w - 1) by omega, decide_false, Bool.not_false, Bool.true_and,
      ite_eq_right_iff]
    intros h
    simp [show n = 0 by omega]

@[simp] theorem sshiftRight_zero {x : BitVec w} : x.sshiftRight 0 = x := by
  ext i
  simp [getLsbD_sshiftRight]

@[simp] theorem zero_sshiftRight {n : Nat} : (0#w).sshiftRight n = 0#w := by
  ext i
  simp [getLsbD_sshiftRight]

theorem sshiftRight_add {x : BitVec w} {m n : Nat} :
    x.sshiftRight (m + n) = (x.sshiftRight m).sshiftRight n := by
  ext i
  simp only [getLsbD_sshiftRight, Nat.add_assoc]
  by_cases h₁ : w ≤ (i : Nat)
  · simp [h₁]
  · simp only [h₁, decide_false, Bool.not_false, Bool.true_and]
    by_cases h₂ : n + ↑i < w
    · simp [h₂]
    · simp only [h₂, ↓reduceIte]
      by_cases h₃ : m + (n + ↑i) < w
      · simp [h₃]
        omega
      · simp [h₃, msb_sshiftRight]

theorem not_sshiftRight {b : BitVec w} :
    ~~~b.sshiftRight n = (~~~b).sshiftRight n := by
  ext i
  simp only [getLsbD_not, Fin.is_lt, decide_true, getLsbD_sshiftRight, Bool.not_and, Bool.not_not,
    Bool.true_and, msb_not]
  by_cases h : w ≤ i
  <;> by_cases h' : n + i < w
  <;> by_cases h'' : 0 < w
  <;> simp [h, h', h'']
  <;> omega

@[simp]
theorem not_sshiftRight_not {x : BitVec w} {n : Nat} :
    ~~~((~~~x).sshiftRight n) = x.sshiftRight n := by
  simp [not_sshiftRight]

@[simp]
theorem getMsbD_sshiftRight {x : BitVec w} {i n : Nat} :
    getMsbD (x.sshiftRight n) i = (decide (i < w) && if i < n then x.msb else getMsbD x (i - n)) := by
  simp only [getMsbD, BitVec.getLsbD_sshiftRight]
  by_cases h : i < w
  · simp only [h, decide_true, Bool.true_and]
    by_cases h₁ : w ≤ w - 1 - i
    · simp [h₁]
      omega
    · simp only [h₁, decide_false, Bool.not_false, Bool.true_and]
      by_cases h₂ : i < n
      · simp only [h₂, ↓reduceIte, ite_eq_right_iff]
        omega
      · simp only [show i - n < w by omega, h₂, ↓reduceIte, decide_true, Bool.true_and]
        by_cases h₄ : n + (w - 1 - i) < w <;> (simp only [h₄, ↓reduceIte]; congr; omega)
  · simp [h]

/-! ### sshiftRight reductions from BitVec to Nat -/

@[simp]
theorem sshiftRight_eq' (x : BitVec w) : x.sshiftRight' y = x.sshiftRight y.toNat := rfl

@[simp]
theorem getLsbD_sshiftRight' {x y: BitVec w} {i : Nat} :
    getLsbD (x.sshiftRight' y) i =
      (!decide (w ≤ i) && if y.toNat + i < w then x.getLsbD (y.toNat + i) else x.msb) := by
  simp only [BitVec.sshiftRight', BitVec.getLsbD_sshiftRight]

@[simp]
theorem getMsbD_sshiftRight' {x y: BitVec w} {i : Nat} :
    (x.sshiftRight y.toNat).getMsbD i = (decide (i < w) && if i < y.toNat then x.msb else x.getMsbD (i - y.toNat)) := by
  simp only [BitVec.sshiftRight', getMsbD, BitVec.getLsbD_sshiftRight]
  by_cases h : i < w
  · simp only [h, decide_true, Bool.true_and]
    by_cases h₁ : w ≤ w - 1 - i
    · simp [h₁]
      omega
    · simp only [h₁, decide_false, Bool.not_false, Bool.true_and]
      by_cases h₂ : i < y.toNat
      · simp only [h₂, ↓reduceIte, ite_eq_right_iff]
        omega
      · simp only [show i - y.toNat < w by omega, h₂, ↓reduceIte, decide_true, Bool.true_and]
        by_cases h₄ : y.toNat + (w - 1 - i) < w <;> (simp only [h₄, ↓reduceIte]; congr; omega)
  · simp [h]

@[simp]
theorem msb_sshiftRight' {x y: BitVec w} :
    (x.sshiftRight' y).msb = x.msb := by
  simp [BitVec.sshiftRight', BitVec.msb_sshiftRight]

/-! ### signExtend -/

/-- Equation theorem for `Int.sub` when both arguments are `Int.ofNat` -/
private theorem Int.ofNat_sub_ofNat_of_lt {n m : Nat} (hlt : n < m) :
    (n : Int) - (m : Int) = -(↑(m - 1 - n) + 1) := by
  omega

/-- Equation theorem for `Int.mod` -/
private theorem Int.negSucc_emod (m : Nat) (n : Int) :
    -(m + 1) % n = Int.subNatNat (Int.natAbs n) ((m % Int.natAbs n) + 1) := rfl

/-- The sign extension is the same as zero extending when `msb = false`. -/
theorem signExtend_eq_not_setWidth_not_of_msb_false {x : BitVec w} {v : Nat} (hmsb : x.msb = false) :
    x.signExtend v = x.setWidth v := by
  ext i
  by_cases hv : i < v
  · simp only [signExtend, getLsbD, getLsbD_setWidth, hv, decide_true, Bool.true_and, toNat_ofInt,
      BitVec.toInt_eq_msb_cond, hmsb, ↓reduceIte, reduceCtorEq]
    rw [Int.ofNat_mod_ofNat, Int.toNat_ofNat, Nat.testBit_mod_two_pow]
    simp [BitVec.testBit_toNat]
  · simp only [getLsbD_setWidth, hv, decide_false, Bool.false_and]
    apply getLsbD_ge
    omega

/--
The sign extension is a bitwise not, followed by a zero extend, followed by another bitwise not
when `msb = true`. The double bitwise not ensures that the high bits are '1',
and the lower bits are preserved. -/
theorem signExtend_eq_not_setWidth_not_of_msb_true {x : BitVec w} {v : Nat} (hmsb : x.msb = true) :
    x.signExtend v = ~~~((~~~x).setWidth v) := by
  apply BitVec.eq_of_toNat_eq
  simp only [signExtend, BitVec.toInt_eq_msb_cond, toNat_ofInt, toNat_not,
    toNat_setWidth, hmsb, ↓reduceIte]
  norm_cast
  rw [Int.ofNat_sub_ofNat_of_lt, Int.negSucc_emod]
  simp only [Int.natAbs_ofNat, Nat.succ_eq_add_one]
  rw [Int.subNatNat_of_le]
  · rw [Int.toNat_ofNat, Nat.add_comm, Nat.sub_add_eq]
  · apply Nat.le_trans
    · apply Nat.succ_le_of_lt
      apply Nat.mod_lt
      apply Nat.two_pow_pos
    · apply Nat.le_refl
  · omega

theorem getLsbD_signExtend (x  : BitVec w) {v i : Nat} :
    (x.signExtend v).getLsbD i = (decide (i < v) && if i < w then x.getLsbD i else x.msb) := by
  rcases hmsb : x.msb with rfl | rfl
  · rw [signExtend_eq_not_setWidth_not_of_msb_false hmsb]
    by_cases (i < v) <;> by_cases (i < w) <;> simp_all <;> omega
  · rw [signExtend_eq_not_setWidth_not_of_msb_true hmsb]
    by_cases (i < v) <;> by_cases (i < w) <;> simp_all <;> omega

theorem getElem_signExtend {x  : BitVec w} {v i : Nat} (h : i < v) :
    (x.signExtend v)[i] = if i < w then x.getLsbD i else x.msb := by
  rw [←getLsbD_eq_getElem, getLsbD_signExtend]
  simp [h]

/-- Sign extending to a width smaller than the starting width is a truncation. -/
theorem signExtend_eq_setWidth_of_lt (x : BitVec w) {v : Nat} (hv : v ≤ w):
  x.signExtend v = x.setWidth v := by
  ext i
  simp only [getLsbD_signExtend, Fin.is_lt, decide_true, Bool.true_and, getLsbD_setWidth,
    ite_eq_left_iff, Nat.not_lt]
  omega

/-- Sign extending to the same bitwidth is a no op. -/
theorem signExtend_eq (x : BitVec w) : x.signExtend w = x := by
  rw [signExtend_eq_setWidth_of_lt _ (Nat.le_refl _), setWidth_eq]

/-! ### append -/

theorem append_def (x : BitVec v) (y : BitVec w) :
    x ++ y = (shiftLeftZeroExtend x w ||| setWidth' (Nat.le_add_left w v) y) := rfl

@[simp] theorem toNat_append (x : BitVec m) (y : BitVec n) :
    (x ++ y).toNat = x.toNat <<< n ||| y.toNat :=
  rfl

theorem getLsbD_append {x : BitVec n} {y : BitVec m} :
    getLsbD (x ++ y) i = bif i < m then getLsbD y i else getLsbD x (i - m) := by
  simp only [append_def, getLsbD_or, getLsbD_shiftLeftZeroExtend, getLsbD_setWidth']
  by_cases h : i < m
  · simp [h]
  · simp_all [h]

theorem getElem_append {x : BitVec n} {y : BitVec m} (h : i < n + m) :
    (x ++ y)[i] = bif i < m then getLsbD y i else getLsbD x (i - m) := by
  simp only [append_def, getElem_or, getElem_shiftLeftZeroExtend, getElem_setWidth']
  by_cases h' : i < m
  · simp [h']
  · simp_all [h']

@[simp] theorem getMsbD_append {x : BitVec n} {y : BitVec m} :
    getMsbD (x ++ y) i = bif n ≤ i then getMsbD y (i - n) else getMsbD x i := by
  simp only [append_def]
  by_cases h : n ≤ i
  · simp [h]
  · simp [h]

theorem msb_append {x : BitVec w} {y : BitVec v} :
    (x ++ y).msb = bif (w == 0) then (y.msb) else (x.msb) := by
  rw [← append_eq, append]
  simp only [msb_or, msb_shiftLeftZeroExtend, msb_setWidth']
  by_cases h : w = 0
  · subst h
    simp [BitVec.msb, getMsbD]
  · rw [cond_eq_if]
    have q : 0 < w + v := by omega
    have t : y.getLsbD (w + v - 1) = false := getLsbD_ge _ _ (by omega)
    simp [h, q, t, BitVec.msb, getMsbD]

@[simp] theorem append_zero_width (x : BitVec w) (y : BitVec 0) : x ++ y = x := by
  ext
  rw [getLsbD_append] -- Why does this not work with `simp [getLsbD_append]`?
  simp

@[simp] theorem zero_width_append (x : BitVec 0) (y : BitVec v) : x ++ y = cast (by omega) y := by
  ext
  rw [getLsbD_append]
  simpa using lt_of_getLsbD

@[simp] theorem zero_append_zero : 0#v ++ 0#w = 0#(v + w) := by
  ext
  simp only [getLsbD_append, getLsbD_zero, Bool.cond_self]

@[simp] theorem cast_append_right (h : w + v = w + v') (x : BitVec w) (y : BitVec v) :
    cast h (x ++ y) = x ++ cast (by omega) y := by
  ext
  simp only [getLsbD_cast, getLsbD_append, cond_eq_if, decide_eq_true_eq]
  split <;> split
  · rfl
  · omega
  · omega
  · congr
    omega

@[simp] theorem cast_append_left (h : w + v = w' + v) (x : BitVec w) (y : BitVec v) :
    cast h (x ++ y) = cast (by omega) x ++ y := by
  ext
  simp [getLsbD_append]

theorem setWidth_append {x : BitVec w} {y : BitVec v} :
    (x ++ y).setWidth k = if h : k ≤ v then y.setWidth k else (x.setWidth (k - v) ++ y).cast (by omega) := by
  apply eq_of_getLsbD_eq
  intro i
  simp only [getLsbD_setWidth, Fin.is_lt, decide_true, getLsbD_append, Bool.true_and]
  split
  · have t : i < v := by omega
    simp [t]
  · by_cases t : i < v
    · simp [t, getLsbD_append]
    · have t' : i - v < k - v := by omega
      simp [t, t', getLsbD_append]

@[simp] theorem setWidth_append_of_eq {x : BitVec v} {y : BitVec w} (h : w' = w) : setWidth (v' + w') (x ++ y) = setWidth v' x ++ setWidth w' y := by
  subst h
  ext i
  simp only [getLsbD_setWidth, Fin.is_lt, decide_true, getLsbD_append, cond_eq_if,
    decide_eq_true_eq, Bool.true_and, setWidth_eq]
  split
  · simp_all
  · simp_all only [Bool.iff_and_self, decide_eq_true_eq]
    intro h
    have := BitVec.lt_of_getLsbD h
    omega

@[simp] theorem setWidth_cons {x : BitVec w} : (cons a x).setWidth w = x := by
  simp [cons, setWidth_append]

@[simp] theorem not_append {x : BitVec w} {y : BitVec v} : ~~~ (x ++ y) = (~~~ x) ++ (~~~ y) := by
  ext i
  simp only [getLsbD_not, getLsbD_append, cond_eq_if]
  split
  · simp_all
  · simp_all; omega

@[simp] theorem and_append {x₁ x₂ : BitVec w} {y₁ y₂ : BitVec v} :
    (x₁ ++ y₁) &&& (x₂ ++ y₂) = (x₁ &&& x₂) ++ (y₁ &&& y₂) := by
  ext i
  simp only [getLsbD_append, cond_eq_if]
  split <;> simp [getLsbD_append, *]

@[simp] theorem or_append {x₁ x₂ : BitVec w} {y₁ y₂ : BitVec v} :
    (x₁ ++ y₁) ||| (x₂ ++ y₂) = (x₁ ||| x₂) ++ (y₁ ||| y₂) := by
  ext i
  simp only [getLsbD_append, cond_eq_if]
  split <;> simp [getLsbD_append, *]

@[simp] theorem xor_append {x₁ x₂ : BitVec w} {y₁ y₂ : BitVec v} :
    (x₁ ++ y₁) ^^^ (x₂ ++ y₂) = (x₁ ^^^ x₂) ++ (y₁ ^^^ y₂) := by
  ext i
  simp only [getLsbD_append, cond_eq_if]
  split <;> simp [getLsbD_append, *]

theorem shiftRight_add {w : Nat} (x : BitVec w) (n m : Nat) :
    x >>> (n + m) = (x >>> n) >>> m:= by
  ext i
  simp [Nat.add_assoc n m i]

theorem shiftLeft_ushiftRight {x : BitVec w} {n : Nat}:
    x >>> n <<< n = x &&& BitVec.allOnes w <<< n := by
  induction n generalizing x
  case zero =>
    ext; simp
  case succ n ih =>
    rw [BitVec.shiftLeft_add, Nat.add_comm, BitVec.shiftRight_add, ih,
       Nat.add_comm, BitVec.shiftLeft_add, BitVec.shiftLeft_and_distrib]
    ext i
    by_cases hw : w = 0
    · simp [hw]
    · by_cases hi₂ : i.val = 0
      · simp [hi₂]
      · simp [Nat.lt_one_iff, hi₂, show 1 + (i.val - 1) = i by omega]

@[simp]
theorem msb_shiftLeft {x : BitVec w} {n : Nat} :
    (x <<< n).msb = x.getMsbD n := by
  simp [BitVec.msb]

@[deprecated shiftRight_add (since := "2024-06-02")]
theorem shiftRight_shiftRight {w : Nat} (x : BitVec w) (n m : Nat) :
    (x >>> n) >>> m = x >>> (n + m) := by
  rw [shiftRight_add]

/-! ### rev -/

theorem getLsbD_rev (x : BitVec w) (i : Fin w) :
    x.getLsbD i.rev = x.getMsbD i := by
  simp only [getLsbD, Fin.val_rev, getMsbD, Fin.is_lt, decide_true, Bool.true_and]
  congr 1
  omega

theorem getElem_rev {x : BitVec w} {i : Fin w}:
    x[i.rev] = x.getMsbD i := by
  simp only [Fin.getElem_fin, Fin.val_rev, getMsbD, Fin.is_lt, decide_true, Bool.true_and]
  congr 1
  omega

theorem getMsbD_rev (x : BitVec w) (i : Fin w) :
    x.getMsbD i.rev = x.getLsbD i := by
  simp only [← getLsbD_rev]
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

theorem getLsbD_cons (b : Bool) {n} (x : BitVec n) (i : Nat) :
    getLsbD (cons b x) i = if i = n then b else getLsbD x i := by
  simp only [getLsbD, toNat_cons, Nat.testBit_or, Nat.testBit_shiftLeft, ge_iff_le]
  rcases Nat.lt_trichotomy i n with i_lt_n | i_eq_n | n_lt_i
  · have p1 : ¬(n ≤ i) := by omega
    have p2 : i ≠ n := by omega
    simp [p1, p2]
  · simp only [i_eq_n, ge_iff_le, Nat.le_refl, decide_true, Nat.sub_self, Nat.testBit_zero,
    Bool.true_and, testBit_toNat, getLsbD_ge, Bool.or_false, ↓reduceIte]
    cases b <;> trivial
  · have p1 : i ≠ n := by omega
    have p2 : i - n ≠ 0 := by omega
    simp [p1, p2, Nat.testBit_bool_to_nat]

theorem getElem_cons {b : Bool} {n} {x : BitVec n} {i : Nat} (h : i < n + 1) :
    (cons b x)[i] = if i = n then b else getLsbD x i := by
  simp only [getElem_eq_testBit_toNat, toNat_cons, Nat.testBit_or, getLsbD]
  rw [Nat.testBit_shiftLeft]
  rcases Nat.lt_trichotomy i n with i_lt_n | i_eq_n | n_lt_i
  · have p1 : ¬(n ≤ i) := by omega
    have p2 : i ≠ n := by omega
    simp [p1, p2]
  · simp only [i_eq_n, ge_iff_le, Nat.le_refl, decide_true, Nat.sub_self, Nat.testBit_zero,
    Bool.true_and, testBit_toNat, getLsbD_ge, Bool.or_false, ↓reduceIte]
    cases b <;> trivial
  · have p1 : i ≠ n := by omega
    have p2 : i - n ≠ 0 := by omega
    simp [p1, p2, Nat.testBit_bool_to_nat]

@[simp] theorem msb_cons : (cons a x).msb = a := by
  simp [cons, msb_cast, msb_append]

@[simp] theorem getMsbD_cons_zero : (cons a x).getMsbD 0 = a := by
  rw [← BitVec.msb, msb_cons]

@[simp] theorem getMsbD_cons_succ : (cons a x).getMsbD (i + 1) = x.getMsbD i := by
  simp [cons, Nat.le_add_left 1 i]

theorem setWidth_succ (x : BitVec w) :
    setWidth (i+1) x = cons (getLsbD x i) (setWidth i x) := by
  apply eq_of_getLsbD_eq
  intro j
  simp only [getLsbD_setWidth, getLsbD_cons, j.isLt, decide_true, Bool.true_and]
  if j_eq : j.val = i then
    simp [j_eq]
  else
    have j_lt : j.val < i := Nat.lt_of_le_of_ne (Nat.le_of_succ_le_succ j.isLt) j_eq
    simp [j_eq, j_lt]

@[simp] theorem cons_msb_setWidth (x : BitVec (w+1)) : (cons x.msb (x.setWidth w)) = x := by
  ext i
  simp only [getLsbD_cons]
  split <;> rename_i h
  · simp [BitVec.msb, getMsbD, h]
  · by_cases h' : i < w
    · simp_all
    · omega

@[deprecated "Use the reverse direction of `cons_msb_setWidth`" (since := "2024-09-23")]
theorem eq_msb_cons_setWidth (x : BitVec (w+1)) : x = (cons x.msb (x.setWidth w)) := by
  simp

@[simp] theorem not_cons (x : BitVec w) (b : Bool) : ~~~(cons b x) = cons (!b) (~~~x) := by
  simp [cons]

@[simp] theorem cons_or_cons (x y : BitVec w) (a b : Bool) :
    (cons a x) ||| (cons b y) = cons (a || b) (x ||| y) := by
  ext i
  simp [cons]

@[simp] theorem cons_and_cons (x y : BitVec w) (a b : Bool) :
    (cons a x) &&& (cons b y) = cons (a && b) (x &&& y) := by
  ext i
  simp [cons]

@[simp] theorem cons_xor_cons (x y : BitVec w) (a b : Bool) :
    (cons a x) ^^^ (cons b y) = cons (a ^^ b) (x ^^^ y) := by
  ext i
  simp [cons]

/-! ### concat -/

@[simp] theorem toNat_concat (x : BitVec w) (b : Bool) :
    (concat x b).toNat = x.toNat * 2 + b.toNat := by
  apply Nat.eq_of_testBit_eq
  simp only [concat, toNat_append, Nat.shiftLeft_eq, Nat.pow_one, toNat_ofBool, Nat.testBit_or]
  cases b
  · simp
  · rintro (_ | i)
    <;> simp [Nat.add_mod, Nat.add_comm, Nat.add_mul_div_right, Nat.testBit_add_one]

theorem getLsbD_concat (x : BitVec w) (b : Bool) (i : Nat) :
    (concat x b).getLsbD i = if i = 0 then b else x.getLsbD (i - 1) := by
  simp only [concat, getLsbD, toNat_append, toNat_ofBool, Nat.testBit_or, Nat.shiftLeft_eq]
  cases i
  · simp [Nat.mod_eq_of_lt b.toNat_lt]
  · simp [Nat.div_eq_of_lt b.toNat_lt, Nat.testBit_add_one]

theorem getElem_concat (x : BitVec w) (b : Bool) (i : Nat) (h : i < w + 1) :
    (concat x b)[i] = if i = 0 then b else x.getLsbD (i - 1) := by
  simp only [concat, getElem_eq_testBit_toNat, getLsbD, toNat_append,
    toNat_ofBool, Nat.testBit_or, Nat.shiftLeft_eq]
  cases i
  · simp [Nat.mod_eq_of_lt b.toNat_lt]
  · simp [Nat.div_eq_of_lt b.toNat_lt, Nat.testBit_add_one]

@[simp] theorem getLsbD_concat_zero : (concat x b).getLsbD 0 = b := by
  simp [getLsbD_concat]

@[simp] theorem getElem_concat_zero : (concat x b)[0] = b := by
  simp [getElem_concat]

@[simp] theorem getLsbD_concat_succ : (concat x b).getLsbD (i + 1) = x.getLsbD i := by
  simp [getLsbD_concat]

@[simp] theorem getElem_concat_succ {x : BitVec w} {i : Nat} (h : i < w) :
    (concat x b)[i + 1] = x[i] := by
  simp [getElem_concat, h, getLsbD_eq_getElem]

@[simp] theorem not_concat (x : BitVec w) (b : Bool) : ~~~(concat x b) = concat (~~~x) !b := by
  ext i; cases i using Fin.succRecOn <;> simp [*, Nat.succ_lt_succ]

@[simp] theorem concat_or_concat (x y : BitVec w) (a b : Bool) :
    (concat x a) ||| (concat y b) = concat (x ||| y) (a || b) := by
  ext i; cases i using Fin.succRecOn <;> simp

@[simp] theorem concat_and_concat (x y : BitVec w) (a b : Bool) :
    (concat x a) &&& (concat y b) = concat (x &&& y) (a && b) := by
  ext i; cases i using Fin.succRecOn <;> simp

@[simp] theorem concat_xor_concat (x y : BitVec w) (a b : Bool) :
    (concat x a) ^^^ (concat y b) = concat (x ^^^ y) (a ^^ b) := by
  ext i; cases i using Fin.succRecOn <;> simp

/-! ### shiftConcat -/

theorem getLsbD_shiftConcat (x : BitVec w) (b : Bool) (i : Nat) :
    (shiftConcat x b).getLsbD i
    = (decide (i < w) && (if (i = 0) then b else x.getLsbD (i - 1))) := by
  simp only [shiftConcat, getLsbD_setWidth, getLsbD_concat]

theorem getLsbD_shiftConcat_eq_decide (x : BitVec w) (b : Bool) (i : Nat) :
    (shiftConcat x b).getLsbD i
    = (decide (i < w) && ((decide (i = 0) && b) || (decide (0 < i) && x.getLsbD (i - 1)))) := by
  simp only [getLsbD_shiftConcat]
  split <;> simp [*, show ((0 < i) ↔ ¬(i = 0)) by omega]

theorem shiftRight_sub_one_eq_shiftConcat (n : BitVec w) (hwn : 0 < wn) :
    n >>> (wn - 1) = (n >>> wn).shiftConcat (n.getLsbD (wn - 1)) := by
  ext i
  simp only [getLsbD_ushiftRight, getLsbD_shiftConcat, Fin.is_lt, decide_true, Bool.true_and]
  split
  · simp [*]
  · congr 1; omega

@[simp, bv_toNat]
theorem toNat_shiftConcat {x : BitVec w} {b : Bool} :
    (x.shiftConcat b).toNat
    = (x.toNat <<< 1 + b.toNat) % 2 ^ w  := by
  simp [shiftConcat, Nat.shiftLeft_eq]

/-- `x.shiftConcat b` does not overflow if `x < 2^k` for `k < w`, and so
`x.shiftConcat b |>.toNat = x.toNat * 2 + b.toNat`. -/
theorem toNat_shiftConcat_eq_of_lt {x : BitVec w} {b : Bool} {k : Nat}
    (hk : k < w) (hx : x.toNat < 2 ^ k) :
    (x.shiftConcat b).toNat = x.toNat * 2 + b.toNat := by
  simp only [toNat_shiftConcat, Nat.shiftLeft_eq, Nat.pow_one]
  have : 2 ^ k < 2 ^ w := Nat.pow_lt_pow_of_lt (by omega) (by omega)
  have : 2 ^ k * 2 ≤ 2 ^ w := (Nat.pow_lt_pow_iff_pow_mul_le_pow (by omega)).mp this
  rw [Nat.mod_eq_of_lt (by cases b <;> simp [bv_toNat] <;> omega)]

theorem toNat_shiftConcat_lt_of_lt {x : BitVec w} {b : Bool} {k : Nat}
    (hk : k < w) (hx : x.toNat < 2 ^ k) :
    (x.shiftConcat b).toNat < 2 ^ (k + 1) := by
  rw [toNat_shiftConcat_eq_of_lt hk hx]
  have : 2 ^ (k + 1) ≤ 2 ^ w := Nat.pow_le_pow_of_le_right (by decide) (by assumption)
  have := Bool.toNat_lt b
  omega

@[simp] theorem zero_concat_false : concat 0#w false = 0#(w + 1) := by
  ext
  simp [getLsbD_concat]

@[simp]
theorem getMsbD_concat {i w : Nat} {b : Bool} {x : BitVec w} :
    (x.concat b).getMsbD i = if i < w then x.getMsbD i else decide (i = w) && b := by
  simp only [getMsbD_eq_getLsbD, Nat.add_sub_cancel, getLsbD_concat]
  by_cases h₀ : i = w
  · simp [h₀]
  · by_cases h₁ : i < w
    · simp [h₀, h₁, show ¬ w - i = 0 by omega, show i < w + 1 by omega, Nat.sub_sub, Nat.add_comm]
    · simp only [show w - i = 0 by omega, ↓reduceIte, h₁, h₀, decide_false, Bool.false_and,
        Bool.and_eq_false_imp, decide_eq_true_eq]
      intro
      omega

@[simp]
theorem msb_concat {w : Nat} {b : Bool} {x : BitVec w} :
    (x.concat b).msb = if 0 < w then x.msb else b := by
  simp only [BitVec.msb, getMsbD_eq_getLsbD, Nat.zero_lt_succ, decide_true, Nat.add_one_sub_one,
    Nat.sub_zero, Bool.true_and]
  by_cases h₀ : 0 < w
  · simp only [Nat.lt_add_one, getLsbD_eq_getElem, getElem_concat, h₀, ↓reduceIte, decide_true,
      Bool.true_and, ite_eq_right_iff]
    intro
    omega
  · simp [h₀, show w = 0 by omega]

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

theorem ofNat_add {n} (x y : Nat) : BitVec.ofNat n (x + y) = BitVec.ofNat n x + BitVec.ofNat n y := by
  apply eq_of_toNat_eq
  simp [BitVec.ofNat, Fin.ofNat'_add]

theorem ofNat_add_ofNat {n} (x y : Nat) : BitVec.ofNat n x + BitVec.ofNat n y = BitVec.ofNat n (x + y) :=
  (ofNat_add x y).symm

protected theorem add_assoc (x y z : BitVec n) : x + y + z = x + (y + z) := by
  apply eq_of_toNat_eq ; simp [Nat.add_assoc]
instance : Std.Associative (α := BitVec n) (· + ·) := ⟨BitVec.add_assoc⟩

protected theorem add_comm (x y : BitVec n) : x + y = y + x := by
  simp [add_def, Nat.add_comm]
instance : Std.Commutative (α := BitVec n) (· + ·) := ⟨BitVec.add_comm⟩

@[simp] protected theorem add_zero (x : BitVec n) : x + 0#n = x := by simp [add_def]

@[simp] protected theorem zero_add (x : BitVec n) : 0#n + x = x := by simp [add_def]
instance : Std.LawfulIdentity (α := BitVec n) (· + ·) 0#n where
  left_id := BitVec.zero_add
  right_id := BitVec.add_zero

theorem setWidth_add (x y : BitVec w) (h : i ≤ w) :
    (x + y).setWidth i = x.setWidth i + y.setWidth i := by
  have dvd : 2^i ∣ 2^w := Nat.pow_dvd_pow _ h
  simp [bv_toNat, h, Nat.mod_mod_of_dvd _ dvd]

@[simp, bv_toNat] theorem toInt_add (x y : BitVec w) :
  (x + y).toInt = (x.toInt + y.toInt).bmod (2^w) := by
  simp [toInt_eq_toNat_bmod]

theorem ofInt_add {n} (x y : Int) : BitVec.ofInt n (x + y) =
    BitVec.ofInt n x + BitVec.ofInt n y := by
  apply eq_of_toInt_eq
  simp

@[simp]
theorem shiftLeft_add_distrib {x y : BitVec w} {n : Nat} :
    (x + y) <<< n = x <<< n + y <<< n := by
  induction n
  case zero =>
    simp
  case succ n ih =>
    simp [ih, toNat_eq, Nat.shiftLeft_eq, ← Nat.add_mul]

theorem add_eq_xor {a b : BitVec 1} : a + b = a ^^^ b := by
  have ha : a = 0 ∨ a = 1 := eq_zero_or_eq_one _
  have hb : b = 0 ∨ b = 1 := eq_zero_or_eq_one _
  rcases ha with h | h <;> (rcases hb with h' | h' <;> (simp [h, h']))

/-! ### sub/neg -/

theorem sub_def {n} (x y : BitVec n) : x - y = .ofNat n ((2^n - y.toNat) + x.toNat) := by rfl

@[simp] theorem toNat_sub {n} (x y : BitVec n) :
    (x - y).toNat = (((2^n - y.toNat) + x.toNat) % 2^n) := rfl

@[simp, bv_toNat] theorem toInt_sub {x y : BitVec w} :
    (x - y).toInt = (x.toInt - y.toInt).bmod (2 ^ w) := by
  simp [toInt_eq_toNat_bmod, @Int.ofNat_sub y.toNat (2 ^ w) (by omega)]

-- We prefer this lemma to `toNat_sub` for the `bv_toNat` simp set.
-- For reasons we don't yet understand, unfolding via `toNat_sub` sometimes
-- results in `omega` generating proof terms that are very slow in the kernel.
@[bv_toNat] theorem toNat_sub' {n} (x y : BitVec n) :
    (x - y).toNat = ((x.toNat + (2^n - y.toNat)) % 2^n) := by
  rw [toNat_sub, Nat.add_comm]

@[simp] theorem toFin_sub (x y : BitVec n) : (x - y).toFin = toFin x - toFin y := rfl

theorem ofFin_sub (x : Fin (2^n)) (y : BitVec n) : .ofFin x - y = .ofFin (x - y.toFin) :=
  rfl
theorem sub_ofFin (x : BitVec n) (y : Fin (2^n)) : x - .ofFin y = .ofFin (x.toFin - y) :=
  rfl

-- Remark: we don't use `[simp]` here because simproc` subsumes it for literals.
-- If `x` and `n` are not literals, applying this theorem eagerly may not be a good idea.
theorem ofNat_sub_ofNat {n} (x y : Nat) : BitVec.ofNat n x - BitVec.ofNat n y = .ofNat n ((2^n - y % 2^n) + x) := by
  apply eq_of_toNat_eq
  simp [BitVec.ofNat, Fin.ofNat'_sub]

@[simp] protected theorem sub_zero (x : BitVec n) : x - 0#n = x := by apply eq_of_toNat_eq ; simp

@[simp] protected theorem zero_sub (x : BitVec n) : 0#n - x = -x := rfl

@[simp] protected theorem sub_self (x : BitVec n) : x - x = 0#n := by
  apply eq_of_toNat_eq
  simp only [toNat_sub]
  rw [Nat.add_comm, Nat.add_sub_of_le]
  · simp
  · exact Nat.le_of_lt x.isLt

@[simp, bv_toNat] theorem toNat_neg (x : BitVec n) : (- x).toNat = (2^n - x.toNat) % 2^n := by
  simp [Neg.neg, BitVec.neg]

theorem toInt_neg {x : BitVec w} :
    (-x).toInt = (-x.toInt).bmod (2 ^ w) := by
  rw [← BitVec.zero_sub, toInt_sub]
  simp [BitVec.toInt_ofNat]

@[simp] theorem toFin_neg (x : BitVec n) :
    (-x).toFin = Fin.ofNat' (2^n) (2^n - x.toNat) :=
  rfl

theorem sub_toAdd {n} (x y : BitVec n) : x - y = x + - y := by
  apply eq_of_toNat_eq
  simp only [toNat_sub, toNat_add, toNat_neg, Nat.add_mod_mod]
  rw [Nat.add_comm]

@[simp] theorem neg_zero (n:Nat) : -BitVec.ofNat n 0 = BitVec.ofNat n 0 := by apply eq_of_toNat_eq ; simp

theorem add_sub_cancel (x y : BitVec w) : x + y - y = x := by
  apply eq_of_toNat_eq
  have y_toNat_le := Nat.le_of_lt y.isLt
  rw [toNat_sub, toNat_add, Nat.add_comm, Nat.mod_add_mod, Nat.add_assoc, ← Nat.add_sub_assoc y_toNat_le,
      Nat.add_sub_cancel_left, Nat.add_mod_right, toNat_mod_cancel]

theorem sub_add_cancel (x y : BitVec w) : x - y + y = x := by
  rw [sub_toAdd, BitVec.add_assoc, BitVec.add_comm _ y,
      ← BitVec.add_assoc, ← sub_toAdd, add_sub_cancel]

theorem eq_sub_iff_add_eq {x y z : BitVec w} : x = z - y ↔ x + y = z := by
  apply Iff.intro <;> intro h
  · simp [h, sub_add_cancel]
  · simp [←h, add_sub_cancel]

theorem negOne_eq_allOnes : -1#w = allOnes w := by
  apply eq_of_toNat_eq
  if g : w = 0 then
    simp [g]
  else
    have q : 1 < 2^w := by simp [g]
    have r : (2^w - 1) < 2^w := by omega
    simp [Nat.mod_eq_of_lt q, Nat.mod_eq_of_lt r]

theorem neg_eq_not_add (x : BitVec w) : -x = ~~~x + 1#w := by
  apply eq_of_toNat_eq
  simp only [toNat_neg, ofNat_eq_ofNat, toNat_add, toNat_not, toNat_ofNat, Nat.add_mod_mod]
  congr
  have hx : x.toNat < 2^w := x.isLt
  rw [Nat.sub_sub, Nat.add_comm 1 x.toNat, ← Nat.sub_sub, Nat.sub_add_cancel (by omega)]

@[simp]
theorem neg_neg {x : BitVec w} : - - x = x := by
  by_cases h : x = 0#w
  · simp [h]
  · simp [bv_toNat, h]

theorem neg_ne_iff_ne_neg {x y : BitVec w} : -x ≠ y ↔ x ≠ -y := by
  constructor
  all_goals
    intro h h'
    subst h'
    simp at h

@[simp]
theorem neg_eq_zero_iff {x : BitVec w} : -x = 0#w ↔ x = 0#w := by
  constructor
  · intro h
    have : - (- x) = - 0 := by simp [h]
    simpa using this
  · intro h
    simp [h]

theorem sub_eq_xor {a b : BitVec 1} : a - b = a ^^^ b := by
  have ha : a = 0 ∨ a = 1 := eq_zero_or_eq_one _
  have hb : b = 0 ∨ b = 1 := eq_zero_or_eq_one _
  rcases ha with h | h <;> (rcases hb with h' | h' <;> (simp [h, h']))

@[simp]
theorem sub_eq_self {x : BitVec 1} : -x = x := by
  have ha : x = 0 ∨ x = 1 := eq_zero_or_eq_one _
  rcases ha with h | h <;> simp [h]

theorem not_neg (x : BitVec w) : ~~~(-x) = x + -1#w := by
  rcases w with _ | w
  · apply Subsingleton.elim
  · rw [BitVec.not_eq_comm]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_neg, BitVec.toNat_not, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.add_mod_mod]
    by_cases hx : x.toNat = 0
    · simp [hx]
    · rw [show (_ - 1 % _) = _ by rw [Nat.mod_eq_of_lt (by omega)],
        show _ + (_ - 1) = (x.toNat - 1) + 2^(w + 1) by omega,
        Nat.add_mod_right,
        show (x.toNat - 1) % _ = _ by rw [Nat.mod_eq_of_lt (by omega)],
        show (_ - x.toNat) % _ = _ by rw [Nat.mod_eq_of_lt (by omega)]]
      omega

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

@[simp]
theorem mul_zero {x : BitVec w} : x * 0#w = 0#w := by
  apply eq_of_toNat_eq
  simp [toNat_mul]

@[simp]
theorem zero_mul {x : BitVec w} : 0#w * x = 0#w := by
  apply eq_of_toNat_eq
  simp [toNat_mul]

theorem mul_add {x y z : BitVec w} :
    x * (y + z) = x * y + x * z := by
  apply eq_of_toNat_eq
  simp only [toNat_mul, toNat_add, Nat.add_mod_mod, Nat.mod_add_mod]
  rw [Nat.mul_mod, Nat.mod_mod (y.toNat + z.toNat),
    ← Nat.mul_mod, Nat.mul_add]

theorem mul_succ {x y : BitVec w} : x * (y + 1#w) = x * y + x := by simp [mul_add]
theorem succ_mul {x y : BitVec w} : (x + 1#w) * y = x * y + y := by simp [BitVec.mul_comm, BitVec.mul_add]

theorem mul_two {x : BitVec w} : x * 2#w = x + x := by
  have : 2#w = 1#w + 1#w := by apply BitVec.eq_of_toNat_eq; simp
  simp [this, mul_succ]

theorem two_mul {x : BitVec w} : 2#w * x = x + x := by rw [BitVec.mul_comm, mul_two]

@[simp, bv_toNat] theorem toInt_mul (x y : BitVec w) :
  (x * y).toInt = (x.toInt * y.toInt).bmod (2^w) := by
  simp [toInt_eq_toNat_bmod]

theorem ofInt_mul {n} (x y : Int) : BitVec.ofInt n (x * y) =
    BitVec.ofInt n x * BitVec.ofInt n y := by
  apply eq_of_toInt_eq
  simp

theorem mul_eq_and {a b : BitVec 1} : a * b = a &&& b := by
  have ha : a = 0 ∨ a = 1 := eq_zero_or_eq_one _
  have hb : b = 0 ∨ b = 1 := eq_zero_or_eq_one _
  rcases ha with h | h <;> (rcases hb with h' | h' <;> (simp [h, h']))

/-! ### le and lt -/

@[bv_toNat] theorem le_def {x y : BitVec n} :
  x ≤ y ↔ x.toNat ≤ y.toNat := Iff.rfl

@[simp] theorem le_ofFin {x : BitVec n} {y : Fin (2^n)} :
  x ≤ BitVec.ofFin y ↔ x.toFin ≤ y := Iff.rfl
@[simp] theorem ofFin_le {x : Fin (2^n)} {y : BitVec n} :
  BitVec.ofFin x ≤ y ↔ x ≤ y.toFin := Iff.rfl
@[simp] theorem ofNat_le_ofNat {n} {x y : Nat} : (BitVec.ofNat n x) ≤ (BitVec.ofNat n y) ↔ x % 2^n ≤ y % 2^n := by
  simp [le_def]

@[bv_toNat] theorem lt_def {x y : BitVec n} :
  x < y ↔ x.toNat < y.toNat := Iff.rfl

@[simp] theorem lt_ofFin {x : BitVec n} {y : Fin (2^n)} :
  x < BitVec.ofFin y ↔ x.toFin < y := Iff.rfl
@[simp] theorem ofFin_lt {x : Fin (2^n)} {y : BitVec n} :
  BitVec.ofFin x < y ↔ x < y.toFin := Iff.rfl
@[simp] theorem ofNat_lt_ofNat {n} {x y : Nat} : BitVec.ofNat n x < BitVec.ofNat n y ↔ x % 2^n < y % 2^n := by
  simp [lt_def]

@[simp] protected theorem not_le {x y : BitVec n} : ¬ x ≤ y ↔ y < x := by
  simp [le_def, lt_def]

@[simp] protected theorem not_lt {x y : BitVec n} : ¬ x < y ↔ y ≤ x := by
  simp [le_def, lt_def]

@[simp] protected theorem le_refl (x : BitVec n) : x ≤ x := by
  simp [le_def]

@[simp] protected theorem lt_irrefl (x : BitVec n) : ¬x < x := by
  simp [lt_def]

protected theorem le_trans {x y z : BitVec n} : x ≤ y → y ≤ z → x ≤ z := by
  simp only [le_def]
  apply Nat.le_trans

protected theorem lt_trans {x y z : BitVec n} : x < y → y < z → x < z := by
  simp only [lt_def]
  apply Nat.lt_trans

protected theorem le_total (x y : BitVec n) : x ≤ y ∨ y ≤ x := by
  simp only [le_def]
  apply Nat.le_total

protected theorem le_antisymm {x y : BitVec n} : x ≤ y → y ≤ x → x = y := by
  simp only [le_def, BitVec.toNat_eq]
  apply Nat.le_antisymm

protected theorem lt_asymm {x y : BitVec n} : x < y → ¬ y < x := by
  simp only [lt_def]
  apply Nat.lt_asymm

protected theorem lt_of_le_ne {x y : BitVec n} : x ≤ y → ¬ x = y → x < y := by
  simp only [lt_def, le_def, BitVec.toNat_eq]
  apply Nat.lt_of_le_of_ne

protected theorem ne_of_lt {x y : BitVec n} : x < y → x ≠ y := by
  simp only [lt_def, ne_eq, toNat_eq]
  apply Nat.ne_of_lt

protected theorem umod_lt (x : BitVec n) {y : BitVec n} : 0 < y → x % y < y := by
  simp only [ofNat_eq_ofNat, lt_def, toNat_ofNat, Nat.zero_mod, umod, toNat_ofNatLt]
  apply Nat.mod_lt

theorem not_lt_iff_le {x y : BitVec w} : (¬ x < y) ↔ y ≤ x := by
  constructor <;>
    (intro h; simp only [lt_def, Nat.not_lt, le_def] at h ⊢; omega)

/-! ### udiv -/

theorem udiv_def {x y : BitVec n} : x / y = BitVec.ofNat n (x.toNat / y.toNat) := by
  have h : x.toNat / y.toNat < 2 ^ n := Nat.lt_of_le_of_lt (Nat.div_le_self ..) (by omega)
  rw [← udiv_eq]
  simp [udiv, bv_toNat, h, Nat.mod_eq_of_lt]

@[simp, bv_toNat]
theorem toNat_udiv {x y : BitVec n} : (x / y).toNat = x.toNat / y.toNat := by
  rw [udiv_def]
  by_cases h : y = 0
  · simp [h]
  · rw [toNat_ofNat, Nat.mod_eq_of_lt]
    exact Nat.lt_of_le_of_lt (Nat.div_le_self ..) (by omega)

@[simp]
theorem zero_udiv {x : BitVec w} : (0#w) / x = 0#w := by
  simp [bv_toNat]

@[simp]
theorem udiv_zero {x : BitVec n} : x / 0#n = 0#n := by
  simp [udiv_def]

@[simp]
theorem udiv_one {x : BitVec w} : x / 1#w = x := by
  simp only [udiv_eq, toNat_eq, toNat_udiv, toNat_ofNat]
  cases w
  · simp [eq_nil x]
  · simp

@[simp]
theorem udiv_eq_and {x y : BitVec 1} :
    x / y = (x &&& y) := by
  have hx : x = 0#1 ∨ x = 1#1 := by bv_omega
  have hy : y = 0#1 ∨ y = 1#1 := by bv_omega
  rcases hx with rfl | rfl <;>
    rcases hy with rfl | rfl <;>
      rfl

@[simp]
theorem udiv_self {x : BitVec w} :
    x / x = if x == 0#w then 0#w else 1#w := by
  by_cases h : x = 0#w
  · simp [h]
  · simp only [toNat_eq, toNat_ofNat, Nat.zero_mod] at h
    simp only [udiv_eq, beq_iff_eq, toNat_eq, toNat_ofNat, Nat.zero_mod, h,
      ↓reduceIte, toNat_udiv]
    rw [Nat.div_self (by omega), Nat.mod_eq_of_lt (by omega)]

/-! ### umod -/

theorem umod_def {x y : BitVec n} :
    x % y = BitVec.ofNat n (x.toNat % y.toNat) := by
  rw [← umod_eq]
  have h : x.toNat % y.toNat < 2 ^ n := Nat.lt_of_le_of_lt (Nat.mod_le _ _) x.isLt
  simp [umod, bv_toNat, Nat.mod_eq_of_lt h]

@[simp, bv_toNat]
theorem toNat_umod {x y : BitVec n} :
    (x % y).toNat = x.toNat % y.toNat := rfl

@[simp]
theorem umod_zero {x : BitVec n} : x % 0#n = x := by
  simp [umod_def]

@[simp]
theorem zero_umod {x : BitVec w} : (0#w) % x = 0#w := by
  simp [bv_toNat]

@[simp]
theorem umod_one {x : BitVec w} : x % (1#w) = 0#w := by
  simp only [toNat_eq, toNat_umod, toNat_ofNat, Nat.zero_mod]
  cases w
  · simp [eq_nil x]
  · simp [Nat.mod_one]

@[simp]
theorem umod_self {x : BitVec w} : x % x = 0#w := by
  simp [bv_toNat]

@[simp]
theorem umod_eq_and {x y : BitVec 1} : x % y = x &&& (~~~y) := by
  have hx : x = 0#1 ∨ x = 1#1 := by bv_omega
  have hy : y = 0#1 ∨ y = 1#1 := by bv_omega
  rcases hx with rfl | rfl <;>
    rcases hy with rfl | rfl <;>
      rfl

/-! ### smtUDiv -/

theorem smtUDiv_eq (x y : BitVec w) : smtUDiv x y = if y = 0#w then allOnes w else x / y := by
  simp [smtUDiv]

@[simp]
theorem smtUDiv_zero {x : BitVec n} : x.smtUDiv 0#n = allOnes n := rfl

/-! ### sdiv -/

/-- Equation theorem for `sdiv` in terms of `udiv`. -/
theorem sdiv_eq (x y : BitVec w) : x.sdiv y =
  match x.msb, y.msb with
  | false, false => udiv x y
  | false, true  =>  - (x.udiv (- y))
  | true,  false => - ((- x).udiv y)
  | true,  true  => (- x).udiv (- y) := by
  rw [BitVec.sdiv]
  rcases x.msb <;> rcases y.msb <;> simp

@[bv_toNat]
theorem toNat_sdiv {x y : BitVec w} : (x.sdiv y).toNat =
    match x.msb, y.msb with
    | false, false => (udiv x y).toNat
    | false, true  =>  (- (x.udiv (- y))).toNat
    | true,  false => (- ((- x).udiv y)).toNat
    | true,  true  => ((- x).udiv (- y)).toNat := by
  simp only [sdiv_eq, toNat_udiv]
  by_cases h : x.msb <;> by_cases h' : y.msb <;> simp [h, h']

@[simp]
theorem zero_sdiv {x : BitVec w} : (0#w).sdiv x = 0#w := by
  simp only [sdiv_eq]
  rcases x.msb with msb | msb <;> simp

@[simp]
theorem sdiv_zero {x : BitVec n} : x.sdiv 0#n = 0#n := by
  simp only [sdiv_eq, msb_zero]
  rcases x.msb with msb | msb <;> apply eq_of_toNat_eq <;> simp

@[simp]
theorem sdiv_one {x : BitVec w} : x.sdiv 1#w = x := by
  simp only [sdiv_eq]
  · by_cases h : w = 1
    · subst h
      rcases x.msb with msb | msb <;> simp
    · rcases x.msb with msb | msb <;> simp [h]

theorem sdiv_eq_and (x y : BitVec 1) : x.sdiv y = x &&& y := by
  have hx : x = 0#1 ∨ x = 1#1 := by bv_omega
  have hy : y = 0#1 ∨ y = 1#1 := by bv_omega
  rcases hx with rfl | rfl <;>
    rcases hy with rfl | rfl <;>
      rfl

@[simp]
theorem sdiv_self {x : BitVec w} :
    x.sdiv x = if x == 0#w then 0#w else 1#w := by
  simp [sdiv_eq]
  · by_cases h : w = 1
    · subst h
      rcases x.msb with msb | msb <;> simp
    · rcases x.msb with msb | msb <;> simp [h]

/-! ### smtSDiv -/

theorem smtSDiv_eq (x y : BitVec w) : smtSDiv x y =
  match x.msb, y.msb with
  | false, false => smtUDiv x y
  | false, true  => -(smtUDiv x (-y))
  | true,  false => -(smtUDiv (-x) y)
  | true,  true  => smtUDiv (-x) (-y) := by
  rw [BitVec.smtSDiv]
  rcases x.msb <;> rcases y.msb <;> simp

@[simp]
theorem smtSDiv_zero {x : BitVec n} : x.smtSDiv 0#n = if x.slt 0#n then 1#n else (allOnes n) := by
  rcases hx : x.msb <;> simp [smtSDiv, slt_zero_iff_msb_cond x, hx, ← negOne_eq_allOnes]

/-! ### srem -/

theorem srem_eq (x y : BitVec w) : srem x y =
  match x.msb, y.msb with
  | false, false => x % y
  | false, true  => x % (-y)
  | true,  false => - ((-x) % y)
  | true,  true  => -((-x) % (-y)) := by
  rw [BitVec.srem]
  rcases x.msb <;> rcases y.msb <;> simp

/-! ### smod -/

/-- Equation theorem for `smod` in terms of `umod`. -/
theorem smod_eq (x y : BitVec w) : x.smod y =
  match x.msb, y.msb with
  | false, false => x.umod y
  | false, true =>
    let u := x.umod (- y)
    (if u = 0#w then u else u + y)
  | true, false =>
    let u := umod (- x) y
    (if u = 0#w then u else y - u)
  | true, true => - ((- x).umod (- y)) := by
  rw [BitVec.smod]
  rcases x.msb <;> rcases y.msb <;> simp

@[bv_toNat]
theorem toNat_smod {x y : BitVec w} : (x.smod y).toNat =
    match x.msb, y.msb with
    | false, false => (x.umod y).toNat
    | false, true =>
      let u := x.umod (- y)
      (if u = 0#w then u.toNat else (u + y).toNat)
    | true, false =>
      let u := (-x).umod y
      (if u = 0#w then u.toNat else (y - u).toNat)
    | true, true => (- ((- x).umod (- y))).toNat := by
  simp only [smod_eq, toNat_umod]
  by_cases h : x.msb <;> by_cases h' : y.msb
  <;> by_cases h'' : (-x).umod y = 0#w <;> by_cases h''' : x.umod (-y) = 0#w
  <;> simp only [h, h', h'', h''']
  <;> simp only [umod, toNat_eq, toNat_ofNatLt, toNat_ofNat, Nat.zero_mod] at h'' h'''
  <;> simp [h'', h''']

@[simp]
theorem smod_zero {x : BitVec n} : x.smod 0#n = x := by
  simp only [smod_eq, msb_zero]
  rcases x.msb with msb | msb <;> apply eq_of_toNat_eq
  · simp
  · by_cases h : x = 0#n <;> simp [h]

/-! ### ofBoolList -/

@[simp] theorem getMsbD_ofBoolListBE : (ofBoolListBE bs).getMsbD i = bs.getD i false := by
  induction bs generalizing i <;> cases i <;> simp_all [ofBoolListBE]

@[simp] theorem getLsbD_ofBoolListBE :
    (ofBoolListBE bs).getLsbD i = (decide (i < bs.length) && bs.getD (bs.length - 1 - i) false) := by
  simp [getLsbD_eq_getMsbD]

@[simp] theorem getElem_ofBoolListBE (h : i < bs.length) :
    (ofBoolListBE bs)[i] = bs[bs.length - 1 - i] := by
  rw [← getLsbD_eq_getElem, getLsbD_ofBoolListBE]
  simp only [h, decide_true, List.getD_eq_getElem?_getD, Bool.true_and]
  rw [List.getElem?_eq_getElem (by omega)]
  simp

@[simp] theorem getLsb_ofBoolListLE : (ofBoolListLE bs).getLsbD i = bs.getD i false := by
  induction bs generalizing i <;> cases i <;> simp_all [ofBoolListLE]

@[simp] theorem getMsbD_ofBoolListLE :
    (ofBoolListLE bs).getMsbD i = (decide (i < bs.length) && bs.getD (bs.length - 1 - i) false) := by
  simp [getMsbD_eq_getLsbD]

/-! # Rotate Left -/

/-- rotateLeft is invariant under `mod` by the bitwidth. -/
@[simp]
theorem rotateLeft_mod_eq_rotateLeft {x : BitVec w} {r : Nat} :
    x.rotateLeft (r % w) = x.rotateLeft r := by
  simp only [rotateLeft, Nat.mod_mod]

/-- `rotateLeft` equals the bit fiddling definition of `rotateLeftAux` when the rotation amount is
smaller than the bitwidth. -/
theorem rotateLeft_eq_rotateLeftAux_of_lt {x : BitVec w} {r : Nat} (hr : r < w) :
    x.rotateLeft r = x.rotateLeftAux r := by
  simp only [rotateLeft, Nat.mod_eq_of_lt hr]


/--
Accessing bits in `x.rotateLeft r` the range `[0, r)` is equal to
accessing bits `x` in the range `[w - r, w)`.

Proof by example:
Let x := <6 5 4 3 2 1 0> : BitVec 7.
x.rotateLeft 2 = (<6 5 | 4 3 2 1 0>).rotateLeft 2 = <3 2 1 0 | 6 5>

(x.rotateLeft 2).getLsbD ⟨i, i < 2⟩
= <3 2 1 0 | 6 5>.getLsbD ⟨i, i < 2⟩
= <6 5>[i]
= <6 5 | 4 3 2 1 0>[i + len(<4 3 2 1 0>)]
= <6 5 | 4 3 2 1 0>[i + 7 - 2]
-/
theorem getLsbD_rotateLeftAux_of_le {x : BitVec w} {r : Nat} {i : Nat} (hi : i < r) :
    (x.rotateLeftAux r).getLsbD i = x.getLsbD (w - r + i) := by
  rw [rotateLeftAux, getLsbD_or, getLsbD_ushiftRight]
  simp; omega

/--
Accessing bits in `x.rotateLeft r` the range `[r, w)` is equal to
accessing bits `x` in the range `[0, w - r)`.

Proof by example:
Let x := <6 5 4 3 2 1 0> : BitVec 7.
x.rotateLeft 2 = (<6 5 | 4 3 2 1 0>).rotateLeft 2 = <3 2 1 0 | 6 5>

(x.rotateLeft 2).getLsbD ⟨i, i ≥ 2⟩
= <3 2 1 0 | 6 5>.getLsbD ⟨i, i ≥ 2⟩
= <3 2 1 0>[i - 2]
= <6 5 | 3 2 1 0>[i - 2]

Intuitively, grab the full width (7), then move the marker `|` by `r` to the right `(-2)`
Then, access the bit at `i` from the right `(+i)`.
 -/
theorem getLsbD_rotateLeftAux_of_geq {x : BitVec w} {r : Nat} {i : Nat} (hi : i ≥ r) :
    (x.rotateLeftAux r).getLsbD i = (decide (i < w) && x.getLsbD (i - r)) := by
  rw [rotateLeftAux, getLsbD_or]
  suffices (x >>> (w - r)).getLsbD i = false by
    have hiltr : decide (i < r) = false := by
      simp [hi]
    simp [getLsbD_shiftLeft, Bool.or_false, hi, hiltr, this]
  simp only [getLsbD_ushiftRight]
  apply getLsbD_ge
  omega

/-- When `r < w`, we give a formula for `(x.rotateRight r).getLsbD i`. -/
theorem getLsbD_rotateLeft_of_le {x : BitVec w} {r i : Nat} (hr: r < w) :
    (x.rotateLeft r).getLsbD i =
      cond (i < r)
      (x.getLsbD (w - r + i))
      (decide (i < w) && x.getLsbD (i - r)) := by
  · rw [rotateLeft_eq_rotateLeftAux_of_lt hr]
    by_cases h : i < r
    · simp [h, getLsbD_rotateLeftAux_of_le h]
    · simp [h, getLsbD_rotateLeftAux_of_geq <| Nat.ge_of_not_lt h]

@[simp]
theorem getLsbD_rotateLeft {x : BitVec w} {r i : Nat}  :
    (x.rotateLeft r).getLsbD i =
      cond (i < r % w)
      (x.getLsbD (w - (r % w) + i))
      (decide (i < w) && x.getLsbD (i - (r % w))) := by
  rcases w with ⟨rfl, w⟩
  · simp
  · rw [← rotateLeft_mod_eq_rotateLeft, getLsbD_rotateLeft_of_le (Nat.mod_lt _ (by omega))]

@[simp]
theorem getElem_rotateLeft {x : BitVec w} {r i : Nat} (h : i < w) :
    (x.rotateLeft r)[i] =
      if h' : i < r % w then x[(w - (r % w) + i)] else x[i - (r % w)] := by
  simp [← BitVec.getLsbD_eq_getElem, h]

/-! ## Rotate Right -/

/--
Accessing bits in `x.rotateRight r` the range `[0, w-r)` is equal to
accessing bits `x` in the range `[r, w)`.

Proof by example:
Let x := <6 5 4 3 2 1 0> : BitVec 7.
x.rotateRight 2 = (<6 5 4 3 2 | 1 0>).rotateRight 2 = <1 0 | 6 5 4 3 2>

(x.rotateLeft 2).getLsbD ⟨i, i ≤ 7 - 2⟩
= <1 0 | 6 5 4 3 2>.getLsbD ⟨i, i ≤ 7 - 2⟩
= <6 5 4 3 2>.getLsbD i
= <6 5 4 3 2 | 1 0>[i + 2]
-/
theorem getLsbD_rotateRightAux_of_le {x : BitVec w} {r : Nat} {i : Nat} (hi : i < w - r) :
    (x.rotateRightAux r).getLsbD i = x.getLsbD (r + i) := by
  rw [rotateRightAux, getLsbD_or, getLsbD_ushiftRight]
  suffices (x <<< (w - r)).getLsbD i = false by
    simp only [this, Bool.or_false]
  simp only [getLsbD_shiftLeft, Bool.and_eq_false_imp, Bool.and_eq_true, decide_eq_true_eq,
    Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt, and_imp]
  omega

/--
Accessing bits in `x.rotateRight r` the range `[w-r, w)` is equal to
accessing bits `x` in the range `[0, r)`.

Proof by example:
Let x := <6 5 4 3 2 1 0> : BitVec 7.
x.rotateRight 2 = (<6 5 4 3 2 | 1 0>).rotateRight 2 = <1 0 | 6 5 4 3 2>

(x.rotateLeft 2).getLsbD ⟨i, i ≥ 7 - 2⟩
= <1 0 | 6 5 4 3 2>.getLsbD ⟨i, i ≤ 7 - 2⟩
= <1 0>.getLsbD (i - len(<6 5 4 3 2>)
= <6 5 4 3 2 | 1 0> (i - len<6 4 4 3 2>)
 -/
theorem getLsbD_rotateRightAux_of_geq {x : BitVec w} {r : Nat} {i : Nat} (hi : i ≥ w - r) :
    (x.rotateRightAux r).getLsbD i = (decide (i < w) && x.getLsbD (i - (w - r))) := by
  rw [rotateRightAux, getLsbD_or]
  suffices (x >>> r).getLsbD i = false by
    simp only [this, getLsbD_shiftLeft, Bool.false_or]
    by_cases hiw : i < w
    <;> simp [hiw, hi]
  simp only [getLsbD_ushiftRight]
  apply getLsbD_ge
  omega

/-- `rotateRight` equals the bit fiddling definition of `rotateRightAux` when the rotation amount is
smaller than the bitwidth. -/
theorem rotateRight_eq_rotateRightAux_of_lt {x : BitVec w} {r : Nat} (hr : r < w) :
    x.rotateRight r = x.rotateRightAux r := by
  simp only [rotateRight, Nat.mod_eq_of_lt hr]

/-- rotateRight is invariant under `mod` by the bitwidth. -/
@[simp]
theorem rotateRight_mod_eq_rotateRight {x : BitVec w} {r : Nat} :
    x.rotateRight (r % w) = x.rotateRight r := by
  simp only [rotateRight, Nat.mod_mod]

/-- When `r < w`, we give a formula for `(x.rotateRight r).getLsb i`. -/
theorem getLsbD_rotateRight_of_le {x : BitVec w} {r i : Nat} (hr: r < w) :
    (x.rotateRight r).getLsbD i =
      cond (i < w - r)
      (x.getLsbD (r + i))
      (decide (i < w) && x.getLsbD (i - (w - r))) := by
  · rw [rotateRight_eq_rotateRightAux_of_lt hr]
    by_cases h : i < w - r
    · simp [h, getLsbD_rotateRightAux_of_le h]
    · simp [h, getLsbD_rotateRightAux_of_geq <| Nat.le_of_not_lt h]

@[simp]
theorem getLsbD_rotateRight {x : BitVec w} {r i : Nat} :
    (x.rotateRight r).getLsbD i =
      cond (i < w - (r % w))
      (x.getLsbD ((r % w) + i))
      (decide (i < w) && x.getLsbD (i - (w - (r % w)))) := by
  rcases w with ⟨rfl, w⟩
  · simp
  · rw [← rotateRight_mod_eq_rotateRight, getLsbD_rotateRight_of_le (Nat.mod_lt _ (by omega))]

@[simp]
theorem getElem_rotateRight {x : BitVec w} {r i : Nat} (h : i < w) :
    (x.rotateRight r)[i] = if h' : i < w - (r % w) then x[(r % w) + i] else x[(i - (w - (r % w)))] := by
  simp only [← BitVec.getLsbD_eq_getElem]
  simp [getLsbD_rotateRight, h]

/- ## twoPow -/

theorem twoPow_eq (w : Nat) (i : Nat) : twoPow w i = 1#w <<< i := by
  dsimp [twoPow]

@[simp, bv_toNat]
theorem toNat_twoPow (w : Nat) (i : Nat) : (twoPow w i).toNat = 2^i % 2^w := by
  rcases w with rfl | w
  · simp [Nat.mod_one, toNat_of_zero_length]
  · simp only [twoPow, toNat_shiftLeft, toNat_ofNat]
    have h1 : 1 < 2 ^ (w + 1) := Nat.one_lt_two_pow (by omega)
    rw [Nat.mod_eq_of_lt h1, Nat.shiftLeft_eq, Nat.one_mul]

@[simp]
theorem getLsbD_twoPow (i j : Nat) : (twoPow w i).getLsbD j = ((i < w) && (i = j)) := by
  rcases w with rfl | w
  · simp
  · simp only [twoPow, getLsbD_shiftLeft, getLsbD_ofNat]
    by_cases hj : j < i
    · simp only [hj, decide_true, Bool.not_true, Bool.and_false, Bool.false_and, Bool.false_eq,
      Bool.and_eq_false_imp, decide_eq_true_eq, decide_eq_false_iff_not]
      omega
    · by_cases hi : Nat.testBit 1 (j - i)
      · obtain hi' := Nat.testBit_one_eq_true_iff_self_eq_zero.mp hi
        have hij : j = i := by omega
        simp_all
      · have hij : i ≠ j := by
          intro h; subst h
          simp at hi
        simp_all

@[simp]
theorem getElem_twoPow {i j : Nat} (h : j < w) : (twoPow w i)[j] = decide (j = i) := by
  rw [←getLsbD_eq_getElem, getLsbD_twoPow]
  simp [eq_comm]
  omega

@[simp]
theorem getMsbD_twoPow {i j w: Nat} :
    (twoPow w i).getMsbD j = (decide (i < w) && decide (j = w - i - 1)) := by
  simp only [getMsbD_eq_getLsbD, getLsbD_twoPow]
  by_cases h₀ : i < w <;> by_cases h₁ : j < w <;>
  simp [h₀, h₁] <;> omega

@[simp]
theorem msb_twoPow {i w: Nat} :
    (twoPow w i).msb = (decide (i < w) && decide (i = w - 1)) := by
  simp only [BitVec.msb, getMsbD_eq_getLsbD, Nat.sub_zero, getLsbD_twoPow,
    Bool.and_iff_right_iff_imp, Bool.and_eq_true, decide_eq_true_eq, and_imp]
  intros
  omega

theorem and_twoPow (x : BitVec w) (i : Nat) :
    x &&& (twoPow w i) = if x.getLsbD i then twoPow w i else 0#w := by
  ext j
  simp only [getLsbD_and, getLsbD_twoPow]
  by_cases hj : i = j <;> by_cases hx : x.getLsbD i <;> simp_all

theorem twoPow_and (x : BitVec w) (i : Nat) :
    (twoPow w i) &&& x = if x.getLsbD i then twoPow w i else 0#w := by
  rw [BitVec.and_comm, and_twoPow]

@[simp]
theorem mul_twoPow_eq_shiftLeft (x : BitVec w) (i : Nat) :
    x * (twoPow w i) = x <<< i := by
  apply eq_of_toNat_eq
  simp only [toNat_mul, toNat_twoPow, toNat_shiftLeft, Nat.shiftLeft_eq]
  by_cases hi : i < w
  · have hpow : 2^i < 2^w := Nat.pow_lt_pow_of_lt (by omega) (by omega)
    rw [Nat.mod_eq_of_lt hpow]
  · have hpow : 2 ^ i % 2 ^ w = 0 := by
      rw [Nat.mod_eq_zero_of_dvd]
      apply Nat.pow_dvd_pow 2 (by omega)
    simp [Nat.mul_mod, hpow]

theorem twoPow_zero {w : Nat} : twoPow w 0 = 1#w := by
  apply eq_of_toNat_eq
  simp

theorem shiftLeft_eq_mul_twoPow (x : BitVec w) (n : Nat) :
    x <<< n = x * (BitVec.twoPow w n) := by
  ext i
  simp [getLsbD_shiftLeft, Fin.is_lt, decide_true, Bool.true_and, mul_twoPow_eq_shiftLeft]

/--
The unsigned division of `x` by `2^k` equals shifting `x` right by `k`,
when `k` is less than the bitwidth `w`.
-/
theorem udiv_twoPow_eq_of_lt {w : Nat} {x : BitVec w} {k : Nat} (hk : k < w) : x / (twoPow w k) = x >>> k := by
  have : 2^k < 2^w := Nat.pow_lt_pow_of_lt (by decide) hk
  simp [bv_toNat, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt this]

/- ### cons -/

@[simp] theorem true_cons_zero : cons true 0#w = twoPow (w + 1) w := by
  ext
  simp [getLsbD_cons]
  omega

@[simp] theorem false_cons_zero : cons false 0#w = 0#(w + 1) := by
  ext
  simp [getLsbD_cons]

@[simp] theorem zero_concat_true : concat 0#w true = 1#(w + 1) := by
  ext
  simp [getLsbD_concat]

/- ### setWidth, setWidth, and bitwise operations -/

/--
When the `(i+1)`th bit of `x` is false,
keeping the lower `(i + 1)` bits of `x` equals keeping the lower `i` bits.
-/
theorem setWidth_setWidth_succ_eq_setWidth_setWidth_of_getLsbD_false
  {x : BitVec w} {i : Nat} (hx : x.getLsbD i = false) :
    setWidth w (x.setWidth (i + 1)) =
      setWidth w (x.setWidth i) := by
  ext k
  simp only [getLsbD_setWidth, Fin.is_lt, decide_true, Bool.true_and, getLsbD_or, getLsbD_and]
  by_cases hik : i = k
  · subst hik
    simp [hx]
  · by_cases hik' : k < i + 1 <;> simp [hik'] <;> omega

/--
When the `(i+1)`th bit of `x` is true,
keeping the lower `(i + 1)` bits of `x` equalsk eeping the lower `i` bits
and then performing bitwise-or with `twoPow i = (1 << i)`,
-/
theorem setWidth_setWidth_succ_eq_setWidth_setWidth_or_twoPow_of_getLsbD_true
    {x : BitVec w} {i : Nat} (hx : x.getLsbD i = true) :
    setWidth w (x.setWidth (i + 1)) =
      setWidth w (x.setWidth i) ||| (twoPow w i) := by
  ext k
  simp only [getLsbD_setWidth, Fin.is_lt, decide_true, Bool.true_and, getLsbD_or, getLsbD_and]
  by_cases hik : i = k
  · subst hik
    simp [hx]
  · by_cases hik' : k < i + 1 <;> simp [hik, hik'] <;> omega

/-- Bitwise and of `(x : BitVec w)` with `1#w` equals zero extending `x.lsb` to `w`. -/
theorem and_one_eq_setWidth_ofBool_getLsbD {x : BitVec w} :
    (x &&& 1#w) = setWidth w (ofBool (x.getLsbD 0)) := by
  ext i
  simp only [getLsbD_and, getLsbD_one, getLsbD_setWidth, Fin.is_lt, decide_true, getLsbD_ofBool,
    Bool.true_and]
  by_cases h : ((i : Nat) = 0) <;> simp [h] <;> omega

@[simp]
theorem replicate_zero_eq {x : BitVec w} : x.replicate 0 = 0#0 := by
  simp [replicate]

@[simp]
theorem replicate_succ_eq {x : BitVec w} :
    x.replicate (n + 1) =
    (x ++ replicate n x).cast (by rw [Nat.mul_succ]; omega) := by
  simp [replicate]

/--
If a number `w * n ≤ i < w * (n + 1)`, then `i - w * n` equals `i % w`.
This is true by subtracting `w * n` from the inequality, giving
`0 ≤ i - w * n < w`, which uniquely identifies `i % w`.
-/
private theorem Nat.sub_mul_eq_mod_of_lt_of_le (hlo : w * n ≤ i) (hhi : i < w * (n + 1)) :
    i - w * n = i % w := by
  rw [Nat.mod_def]
  congr
  symm
  apply Nat.div_eq_of_lt_le
    (by rw [Nat.mul_comm]; omega)
    (by rw [Nat.mul_comm]; omega)

@[simp]
theorem getLsbD_replicate {n w : Nat} (x : BitVec w) :
    (x.replicate n).getLsbD i =
    (decide (i < w * n) && x.getLsbD (i % w)) := by
  induction n generalizing x
  case zero => simp
  case succ n ih =>
    simp only [replicate_succ_eq, getLsbD_cast, getLsbD_append]
    by_cases hi : i < w * (n + 1)
    · simp only [hi, decide_true, Bool.true_and]
      by_cases hi' : i < w * n
      · simp [hi', ih]
      · simp only [hi', decide_false, cond_false]
        rw [Nat.sub_mul_eq_mod_of_lt_of_le] <;> omega
    · rw [Nat.mul_succ] at hi ⊢
      simp only [show ¬i < w * n by omega, decide_false, cond_false, hi, Bool.false_and]
      apply BitVec.getLsbD_ge (x := x) (i := i - w * n) (ge := by omega)

@[simp]
theorem getElem_replicate {n w : Nat} (x : BitVec w) (h : i < w * n) :
    (x.replicate n)[i] = if h' : w = 0 then false else x[i % w]'(@Nat.mod_lt i w (by omega)) := by
  simp only [← getLsbD_eq_getElem, getLsbD_replicate]
  by_cases h' : w = 0 <;> simp [h'] <;> omega

/-! ### intMin -/

/-- The bitvector of width `w` that has the smallest value when interpreted as an integer. -/
def intMin (w : Nat) := twoPow w (w - 1)

theorem getLsbD_intMin (w : Nat) : (intMin w).getLsbD i = decide (i + 1 = w) := by
  simp only [intMin, getLsbD_twoPow, boolToPropSimps]
  omega

theorem getMsbD_intMin {w i : Nat} :
    (intMin w).getMsbD i = (decide (0 < w) && decide (i = 0)) := by
  simp only [getMsbD, getLsbD_intMin]
  match w, i with
  | 0,   _    => simp
  | w+1, 0    => simp
  | w+1, i+1  => simp; omega

/--
The RHS is zero in case `w = 0` which is modeled by wrapping the expression in `... % 2 ^ w`.
-/
@[simp, bv_toNat]
theorem toNat_intMin : (intMin w).toNat = 2 ^ (w - 1) % 2 ^ w := by
  simp [intMin]

/--
The RHS is zero in case `w = 0` which is modeled by wrapping the expression in `... % 2 ^ w`.
-/
@[simp]
theorem toInt_intMin {w : Nat} :
    (intMin w).toInt = -((2 ^ (w - 1) % 2 ^ w) : Nat) := by
  by_cases h : w = 0
  · subst h
    simp [BitVec.toInt]
  · have w_pos : 0 < w := by omega
    simp only [BitVec.toInt, toNat_intMin, w_pos, Nat.two_pow_pred_mod_two_pow,
      Int.two_pow_pred_sub_two_pow, ite_eq_right_iff]
    rw [Nat.mul_comm]
    simp [w_pos]

theorem toInt_intMin_le (x : BitVec w) :
    (intMin w).toInt ≤ x.toInt := by
  cases w
  case zero => simp [@of_length_zero x]
  case succ w =>
    simp only [toInt_intMin, Nat.add_one_sub_one, Int.ofNat_emod]
    have : 0 < 2 ^ w := Nat.two_pow_pos w
    rw [Int.emod_eq_of_lt (by omega) (by omega)]
    rw [BitVec.toInt_eq_toNat_bmod]
    rw [show (2 ^ w : Nat) = ((2 ^ (w + 1) : Nat) : Int) / 2 by omega]
    apply Int.le_bmod (by omega)

theorem intMin_sle (x : BitVec w) : (intMin w).sle x := by
  simp only [BitVec.sle, toInt_intMin_le x, decide_true]

@[simp]
theorem neg_intMin {w : Nat} : -intMin w = intMin w := by
  by_cases h : 0 < w
  · simp [bv_toNat, h]
  · simp only [Nat.not_lt, Nat.le_zero_eq] at h
    simp [bv_toNat, h]

@[simp]
theorem abs_intMin {w : Nat} : (intMin w).abs = intMin w := by
  simp [BitVec.abs, bv_toNat]

theorem toInt_neg_of_ne_intMin {x : BitVec w} (rs : x ≠ intMin w) :
    (-x).toInt = -(x.toInt) := by
  simp only [ne_eq, toNat_eq, toNat_intMin] at rs
  by_cases x_zero : x = 0
  · subst x_zero
    simp [BitVec.toInt]
    omega
  by_cases w_0 : w = 0
  · subst w_0
    simp [BitVec.eq_nil x]
  have : 0 < w := by omega
  rw [Nat.two_pow_pred_mod_two_pow (by omega)] at rs
  simp only [BitVec.toInt, BitVec.toNat_neg, BitVec.sub_toNat_mod_cancel x_zero]
  have := @Nat.two_pow_pred_mul_two w (by omega)
  split <;> split <;> omega

theorem msb_intMin {w : Nat} : (intMin w).msb = decide (0 < w) := by
  simp only [msb_eq_decide, toNat_intMin, decide_eq_decide]
  by_cases h : 0 < w <;> simp_all

/-! ### intMax -/

/-- The bitvector of width `w` that has the largest value when interpreted as an integer. -/
def intMax (w : Nat) := (twoPow w (w - 1)) - 1

@[simp, bv_toNat]
theorem toNat_intMax : (intMax w).toNat = 2 ^ (w - 1) - 1 := by
  simp only [intMax]
  by_cases h : w = 0
  · simp [h]
  · have h' : 0 < w := by omega
    rw [toNat_sub, toNat_twoPow, ← Nat.sub_add_comm (by simpa [h'] using Nat.one_le_two_pow),
      Nat.add_sub_assoc (by simpa [h'] using Nat.one_le_two_pow),
      Nat.two_pow_pred_mod_two_pow h', ofNat_eq_ofNat, toNat_ofNat, Nat.one_mod_two_pow h',
      Nat.add_mod_left, Nat.mod_eq_of_lt]
    have := Nat.two_pow_pred_lt_two_pow h'
    have := Nat.two_pow_pos w
    omega

@[simp]
theorem getLsbD_intMax (w : Nat) : (intMax w).getLsbD i = decide (i + 1 < w) := by
  rw [← testBit_toNat, toNat_intMax, Nat.testBit_two_pow_sub_one, decide_eq_decide]
  omega

@[simp] theorem intMax_add_one {w : Nat} : intMax w + 1#w = intMin w := by
  simp only [toNat_eq, toNat_intMax, toNat_add, toNat_intMin, toNat_ofNat, Nat.add_mod_mod]
  by_cases h : w = 0
  · simp [h]
  · rw [Nat.sub_add_cancel (Nat.two_pow_pos (w - 1)), Nat.two_pow_pred_mod_two_pow (by omega)]


/-! ### Non-overflow theorems -/

/-- If `x.toNat * y.toNat < 2^w`, then the multiplication `(x * y)` does not overflow. -/
theorem toNat_add_of_lt {w} {x y : BitVec w} (h : x.toNat + y.toNat < 2^w) :
    (x + y).toNat = x.toNat + y.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

/--
If `y ≤ x`, then the subtraction `(x - y)` does not overflow.
Thus, `(x - y).toNat = x.toNat - y.toNat`
-/
theorem toNat_sub_of_le {x y : BitVec n} (h : y ≤ x) :
    (x - y).toNat = x.toNat - y.toNat := by
  simp only [toNat_sub]
  rw [BitVec.le_def] at h
  by_cases h' : x.toNat = y.toNat
  · rw [h', Nat.sub_self, Nat.sub_add_cancel (by omega), Nat.mod_self]
  · have : 2 ^ n - y.toNat + x.toNat = 2 ^ n + (x.toNat - y.toNat) := by omega
    rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

/--
If `y > x`, then the subtraction `(x - y)` *does* overflow, and the result is the wraparound.
Thus, `(x - y).toNat = 2^w - (y.toNat - x.toNat)`.
-/
theorem toNat_sub_of_lt {x y : BitVec w} (h : x < y) :
    (x - y).toNat = 2^w - (y.toNat - x.toNat) := by
  simp only [toNat_sub]
  rw [Nat.mod_eq_of_lt (by bv_omega)]
  bv_omega

/-- If `x.toNat * y.toNat < 2^w`, then the multiplication `(x * y)` does not overflow.
Thus, `(x * y).toNat = x.toNat * y.toNat`.
-/
theorem toNat_mul_of_lt {w} {x y : BitVec w} (h : x.toNat * y.toNat < 2^w) :
    (x * y).toNat = x.toNat * y.toNat := by
  rw [BitVec.toNat_mul, Nat.mod_eq_of_lt h]


/--
`x ≤ y + z` if and only if `x - z ≤ y`
when `x - z` and `y + z` do not overflow.
-/
theorem le_add_iff_sub_le {x y z : BitVec w}
    (hxz : z ≤ x) (hbz : y.toNat + z.toNat < 2^w) :
      x ≤ y + z ↔ x - z ≤ y := by
  simp_all only [BitVec.le_def]
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega),
    BitVec.toNat_add_of_lt (by omega)]
  omega

/--
`x - z ≤ y - z` if and only if `x ≤ y`
when `x - z` and `y - z` do not overflow.
-/
theorem sub_le_sub_iff_le {x y z : BitVec w} (hxz : z ≤ x) (hyz : z ≤ y) :
    (x - z ≤ y - z) ↔ x ≤ y := by
  simp_all only [BitVec.le_def]
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega),
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)]
  omega

/-! ### neg -/

theorem msb_eq_toInt {x : BitVec w}:
    x.msb = decide (x.toInt < 0) := by
  by_cases h : x.msb <;>
  · simp [h, toInt_eq_msb_cond]
    omega

theorem msb_eq_toNat {x : BitVec w}:
    x.msb = decide (x.toNat ≥ 2 ^ (w - 1)) := by
  simp only [msb_eq_decide, ge_iff_le]

/-! ### abs -/

theorem abs_eq (x : BitVec w) : x.abs = if x.msb then -x else x := by rfl

@[simp, bv_toNat]
theorem toNat_abs {x : BitVec w} : x.abs.toNat = if x.msb then 2^w - x.toNat else x.toNat := by
  simp only [BitVec.abs, neg_eq]
  by_cases h : x.msb = true
  · simp only [h, ↓reduceIte, toNat_neg]
    have : 2 * x.toNat ≥ 2 ^ w := BitVec.msb_eq_true_iff_two_mul_ge.mp h
    rw [Nat.mod_eq_of_lt (by omega)]
  · simp [h]

theorem getLsbD_abs {i : Nat} {x : BitVec w} :
   getLsbD x.abs i = if x.msb then getLsbD (-x) i else getLsbD x i := by
  by_cases h : x.msb <;> simp [BitVec.abs, h]

theorem getMsbD_abs {i : Nat} {x : BitVec w} :
    getMsbD (x.abs) i = if x.msb then getMsbD (-x) i else getMsbD x i := by
  by_cases h : x.msb <;> simp [BitVec.abs, h]

/-! ### Decidable quantifiers -/

theorem forall_zero_iff {P : BitVec 0 → Prop} :
    (∀ v, P v) ↔ P 0#0 := by
  constructor
  · intro h
    apply h
  · intro h v
    obtain (rfl : v = 0#0) := (by ext ⟨i, h⟩; simp at h)
    apply h

theorem forall_cons_iff {P : BitVec (n + 1) → Prop} :
    (∀ v : BitVec (n + 1), P v) ↔ (∀ (x : Bool) (v : BitVec n), P (v.cons x)) := by
  constructor
  · intro h _ _
    apply h
  · intro h v
    have w : v = (v.setWidth n).cons v.msb := by simp
    rw [w]
    apply h

instance instDecidableForallBitVecZero (P : BitVec 0 → Prop) :
    ∀ [Decidable (P 0#0)], Decidable (∀ v, P v)
  | .isTrue h => .isTrue fun v => by
    obtain (rfl : v = 0#0) := (by ext ⟨i, h⟩; cases h)
    exact h
  | .isFalse h => .isFalse (fun w => h (w _))

instance instDecidableForallBitVecSucc (P : BitVec (n+1) → Prop) [DecidablePred P]
    [Decidable (∀ (x : Bool) (v : BitVec n), P (v.cons x))] : Decidable (∀ v, P v) :=
  decidable_of_iff' (∀ x (v : BitVec n), P (v.cons x)) forall_cons_iff

instance instDecidableExistsBitVecZero (P : BitVec 0 → Prop) [Decidable (P 0#0)] :
    Decidable (∃ v, P v) :=
  decidable_of_iff (¬ ∀ v, ¬ P v) Classical.not_forall_not

instance instDecidableExistsBitVecSucc (P : BitVec (n+1) → Prop) [DecidablePred P]
    [Decidable (∀ (x : Bool) (v : BitVec n), ¬ P (v.cons x))] : Decidable (∃ v, P v) :=
  decidable_of_iff (¬ ∀ v, ¬ P v) Classical.not_forall_not

/--
For small numerals this isn't necessary (as typeclass search can use the above two instances),
but for large numerals this provides a shortcut.
Note, however, that for large numerals the decision procedure may be very slow,
and you should use `bv_decide` if possible.
-/
instance instDecidableForallBitVec :
    ∀ (n : Nat) (P : BitVec n → Prop) [DecidablePred P], Decidable (∀ v, P v)
  | 0, _, _ => inferInstance
  | n + 1, _, _ =>
    have := instDecidableForallBitVec n
    inferInstance

/--
For small numerals this isn't necessary (as typeclass search can use the above two instances),
but for large numerals this provides a shortcut.
Note, however, that for large numerals the decision procedure may be very slow.
-/
instance instDecidableExistsBitVec :
    ∀ (n : Nat) (P : BitVec n → Prop) [DecidablePred P], Decidable (∃ v, P v)
  | 0, _, _ => inferInstance
  | n + 1, _, _ =>
    have := instDecidableExistsBitVec n
    inferInstance

/-! ### Deprecations -/

set_option linter.missingDocs false

@[deprecated truncate_eq_setWidth (since := "2024-09-18")]
abbrev truncate_eq_zeroExtend := @truncate_eq_setWidth

@[deprecated toNat_setWidth' (since := "2024-09-18")]
abbrev toNat_zeroExtend' := @toNat_setWidth'

@[deprecated toNat_setWidth (since := "2024-09-18")]
abbrev toNat_zeroExtend := @toNat_setWidth

@[deprecated toNat_setWidth (since := "2024-09-18")]
abbrev toNat_truncate := @toNat_setWidth

@[deprecated setWidth_eq (since := "2024-09-18")]
abbrev zeroExtend_eq := @setWidth_eq

@[deprecated setWidth_eq (since := "2024-09-18")]
abbrev truncate_eq := @setWidth_eq

@[deprecated setWidth_zero (since := "2024-09-18")]
abbrev zeroExtend_zero := @setWidth_zero

@[deprecated getElem_setWidth (since := "2024-09-18")]
abbrev getElem_zeroExtend := @getElem_setWidth

@[deprecated getElem_setWidth' (since := "2024-09-18")]
abbrev getElem_zeroExtend' := @getElem_setWidth'

@[deprecated getElem?_setWidth (since := "2024-09-18")]
abbrev getElem?_zeroExtend := @getElem?_setWidth

@[deprecated getElem?_setWidth' (since := "2024-09-18")]
abbrev getElem?_zeroExtend' := @getElem?_setWidth'

@[deprecated getLsbD_setWidth (since := "2024-09-18")]
abbrev getLsbD_zeroExtend := @getLsbD_setWidth

@[deprecated getLsbD_setWidth' (since := "2024-09-18")]
abbrev getLsbD_zeroExtend' := @getLsbD_setWidth'

@[deprecated getMsbD_setWidth_add (since := "2024-09-18")]
abbrev getMsbD_zeroExtend_add := @getMsbD_setWidth_add

@[deprecated getMsbD_setWidth' (since := "2024-09-18")]
abbrev getMsbD_zeroExtend' := @getMsbD_setWidth'

@[deprecated getElem_setWidth (since := "2024-09-18")]
abbrev getElem_truncate := @getElem_setWidth

@[deprecated getElem?_setWidth (since := "2024-09-18")]
abbrev getElem?_truncate := @getElem?_setWidth

@[deprecated getLsbD_setWidth (since := "2024-09-18")]
abbrev getLsbD_truncate := @getLsbD_setWidth

@[deprecated msb_setWidth (since := "2024-09-18")]
abbrev msb_truncate := @msb_setWidth

@[deprecated cast_setWidth (since := "2024-09-18")]
abbrev cast_zeroExtend := @cast_setWidth

@[deprecated cast_setWidth (since := "2024-09-18")]
abbrev cast_truncate := @cast_setWidth

@[deprecated setWidth_setWidth_of_le (since := "2024-09-18")]
abbrev zeroExtend_zeroExtend_of_le := @setWidth_setWidth_of_le

@[deprecated setWidth_eq (since := "2024-09-18")]
abbrev truncate_eq_self := @setWidth_eq

@[deprecated setWidth_cast (since := "2024-09-18")]
abbrev truncate_cast := @setWidth_cast

@[deprecated msb_setWidth (since := "2024-09-18")]
abbrev mbs_zeroExtend := @msb_setWidth

@[deprecated msb_setWidth' (since := "2024-09-18")]
abbrev mbs_zeroExtend' := @msb_setWidth'

@[deprecated setWidth_one_eq_ofBool_getLsb_zero (since := "2024-09-18")]
abbrev zeroExtend_one_eq_ofBool_getLsb_zero := @setWidth_one_eq_ofBool_getLsb_zero

@[deprecated setWidth_ofNat_one_eq_ofNat_one_of_lt (since := "2024-09-18")]
abbrev zeroExtend_ofNat_one_eq_ofNat_one_of_lt := @setWidth_ofNat_one_eq_ofNat_one_of_lt

@[deprecated setWidth_one (since := "2024-09-18")]
abbrev truncate_one := @setWidth_one

@[deprecated setWidth_ofNat_of_le (since := "2024-09-18")]
abbrev truncate_ofNat_of_le := @setWidth_ofNat_of_le

@[deprecated setWidth_or (since := "2024-09-18")]
abbrev truncate_or := @setWidth_or

@[deprecated setWidth_and (since := "2024-09-18")]
abbrev truncate_and := @setWidth_and

@[deprecated setWidth_xor (since := "2024-09-18")]
abbrev truncate_xor := @setWidth_xor

@[deprecated setWidth_not (since := "2024-09-18")]
abbrev truncate_not := @setWidth_not

@[deprecated signExtend_eq_not_setWidth_not_of_msb_false  (since := "2024-09-18")]
abbrev signExtend_eq_not_zeroExtend_not_of_msb_false  := @signExtend_eq_not_setWidth_not_of_msb_false

@[deprecated signExtend_eq_not_setWidth_not_of_msb_true (since := "2024-09-18")]
abbrev signExtend_eq_not_zeroExtend_not_of_msb_true := @signExtend_eq_not_setWidth_not_of_msb_true

@[deprecated signExtend_eq_setWidth_of_lt (since := "2024-09-18")]
abbrev signExtend_eq_truncate_of_lt := @signExtend_eq_setWidth_of_lt

@[deprecated truncate_append (since := "2024-09-18")]
abbrev truncate_append := @setWidth_append

@[deprecated truncate_append_of_eq (since := "2024-09-18")]
abbrev truncate_append_of_eq := @setWidth_append_of_eq

@[deprecated truncate_cons (since := "2024-09-18")]
abbrev truncate_cons := @setWidth_cons

@[deprecated truncate_succ (since := "2024-09-18")]
abbrev truncate_succ := @setWidth_succ

@[deprecated truncate_add (since := "2024-09-18")]
abbrev truncate_add := @setWidth_add

@[deprecated setWidth_setWidth_succ_eq_setWidth_setWidth_of_getLsbD_false (since := "2024-09-18")]
abbrev zeroExtend_truncate_succ_eq_zeroExtend_truncate_of_getLsbD_false := @setWidth_setWidth_succ_eq_setWidth_setWidth_of_getLsbD_false

@[deprecated setWidth_setWidth_succ_eq_setWidth_setWidth_or_twoPow_of_getLsbD_true (since := "2024-09-18")]
abbrev zeroExtend_truncate_succ_eq_zeroExtend_truncate_or_twoPow_of_getLsbD_true := @setWidth_setWidth_succ_eq_setWidth_setWidth_or_twoPow_of_getLsbD_true

@[deprecated and_one_eq_setWidth_ofBool_getLsbD (since := "2024-09-18")]
abbrev and_one_eq_zeroExtend_ofBool_getLsbD := @and_one_eq_setWidth_ofBool_getLsbD

@[deprecated msb_sshiftRight (since := "2024-10-03")]
abbrev sshiftRight_msb_eq_msb := @msb_sshiftRight

@[deprecated shiftLeft_zero (since := "2024-10-27")]
abbrev shiftLeft_zero_eq := @shiftLeft_zero

@[deprecated ushiftRight_zero (since := "2024-10-27")]
abbrev ushiftRight_zero_eq := @ushiftRight_zero

end BitVec
