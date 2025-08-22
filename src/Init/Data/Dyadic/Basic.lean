/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Robin Arnez
-/
module

prelude
public import Init.Data.Rat.Lemmas

/-!
# The dyadic rationals

Constructs the dyadic rationals as an ordered ring, equipped with a compatible embedding into the rationals.
-/

set_option linter.missingDocs true

@[expose] public section

open Nat

namespace Int

/-- The number of trailing zeros in the binary representation of `i`. -/
def trailingZeros (i : Int) : Nat :=
  if h : i = 0 then 0 else aux i.natAbs i h (Nat.le_refl _) 0
where
  aux (k : Nat) (i : Int) (hi : i ≠ 0) (hk : i.natAbs ≤ k) (acc : Nat) : Nat :=
    match k, (by omega : k ≠ 0) with
    | k + 1, _ =>
      if h : i % 2 = 0 then aux k (i / 2) (by omega) (by omega) (acc + 1)
      else acc

-- TODO: check performance of `trailingZeros` in the kernel and VM.

private theorem trailingZeros_aux_irrel (hi : i ≠ 0) (hk : i.natAbs ≤ k) (hk' : i.natAbs ≤ k') :
    trailingZeros.aux k i hi hk acc = trailingZeros.aux k' i hi hk' acc := by
  fun_induction trailingZeros.aux k i hi hk acc generalizing k' <;>
    fun_cases trailingZeros.aux k' _ _ hk' _
  · rename_i ih _ _ _ _ _
    exact ih _
  · contradiction
  · contradiction
  · rfl

private theorem trailingZeros_aux_succ :
    trailingZeros.aux k i hi hk (acc + 1) = trailingZeros.aux k i hi hk acc + 1 := by
  fun_induction trailingZeros.aux k i hi hk acc <;> simp_all [trailingZeros.aux]

theorem trailingZeros_zero : trailingZeros 0 = 0 := rfl

theorem trailingZeros_two_mul_add_one (i : Int) :
    Int.trailingZeros (2 * i + 1) = 0 := by
  unfold trailingZeros trailingZeros.aux
  rw [dif_neg (by omega)]
  split <;> simp_all

theorem trailingZeros_eq_zero_of_mod_eq {i : Int} (h : i % 2 = 1) :
    Int.trailingZeros i = 0 := by
  unfold trailingZeros trailingZeros.aux
  rw [dif_neg (by omega)]
  split <;> simp_all

theorem trailingZeros_two_mul {i : Int} (h : i ≠ 0) :
    Int.trailingZeros (2 * i) = Int.trailingZeros i + 1 := by
  rw [Int.trailingZeros, dif_neg (Int.mul_ne_zero (by decide) h), Int.trailingZeros.aux.eq_def]
  simp only [ne_eq, mul_emod_right, ↓reduceDIte, Int.reduceEq, not_false_eq_true,
    mul_ediv_cancel_left, Nat.zero_add]
  split
  rw [trailingZeros, trailingZeros_aux_succ, dif_neg h]
  apply congrArg Nat.succ (trailingZeros_aux_irrel ..) <;> omega

theorem shiftRight_trailingZeros_mod_two {i : Int} (h : i ≠ 0) :
    (i >>> i.trailingZeros) % 2 = 1 := by
  rw (occs := .pos [2]) [← Int.emod_add_ediv i 2]
  rcases i.emod_two_eq with h' | h' <;> rw [h']
  · rcases Int.dvd_of_emod_eq_zero h' with ⟨a, rfl⟩
    simp only [ne_eq, Int.mul_eq_zero, Int.reduceEq, false_or] at h
    rw [Int.zero_add, mul_ediv_cancel_left _ (by decide), trailingZeros_two_mul h, Nat.add_comm,
      shiftRight_add, shiftRight_eq_div_pow _ 1]
    simpa using shiftRight_trailingZeros_mod_two h
  · rwa [Int.add_comm, trailingZeros_two_mul_add_one, shiftRight_zero]
termination_by i.natAbs

theorem two_pow_trailingZeros_dvd {i : Int} (h : i ≠ 0) :
    2 ^ i.trailingZeros ∣ i := by
  rcases i.emod_two_eq with h' | h'
  · rcases Int.dvd_of_emod_eq_zero h' with ⟨a, rfl⟩
    simp only [ne_eq, Int.mul_eq_zero, Int.reduceEq, false_or] at h
    rw [trailingZeros_two_mul h, Int.pow_succ']
    exact Int.mul_dvd_mul_left _ (two_pow_trailingZeros_dvd h)
  · rw (occs := .pos [1]) [← Int.emod_add_ediv i 2, h', Int.add_comm, trailingZeros_two_mul_add_one]
    exact Int.one_dvd _
termination_by i.natAbs

theorem trailingZeros_shiftLeft {x : Int} (hx : x ≠ 0) (n : Nat) :
    trailingZeros (x <<< n) = x.trailingZeros + n := by
  have : NeZero x := ⟨hx⟩
  induction n <;> simp [Int.shiftLeft_succ', trailingZeros_two_mul (NeZero.ne _), *, Nat.add_assoc]

end Int

/--
A dyadic rational is either zero or of the form `n * 2^(-k)` for some (unique) `n k : Int`
where `n` is odd.
-/
inductive Dyadic where
  /-- The dyadic number `0`. -/
  | zero
  /-- The dyadic number `n * 2^(-k)` for some odd `n` and integer `k`. -/
  | ofOdd (n : Int) (k : Int) (hn : n % 2 = 1)
deriving DecidableEq

/-- Returns the dyadic number representation of `i * 2 ^ (-exp)`. -/
def Dyadic.ofIntWithPrec (i : Int) (prec : Int) : Dyadic :=
  if h : i = 0 then .zero
  else .ofOdd (i >>> i.trailingZeros) (prec - i.trailingZeros) (Int.shiftRight_trailingZeros_mod_two h)

/-- Convert an integer to a dyadic number (which will necessarily have non-positive precision). -/
def Dyadic.ofInt (i : Int) : Dyadic :=
  Dyadic.ofIntWithPrec i 0

namespace Dyadic

instance (n : Nat) : OfNat Dyadic n where
  ofNat := Dyadic.ofInt n

/-- Add two dyadic numbers. -/
protected def add (x y : Dyadic) : Dyadic :=
  match x, y with
  | .zero, y => y
  | x, .zero => x
  | .ofOdd n₁ k₁ hn₁, .ofOdd n₂ k₂ hn₂ =>
    match k₁ - k₂ with
    | 0 => .ofIntWithPrec (n₁ + n₂) k₁
    | (d@hd:(d' + 1) : Nat) => .ofOdd (n₁ + (n₂ <<< d)) k₁ ?_
    | -(d + 1 : Nat) => .ofOdd (n₁ <<< (d + 1) + n₂) k₂ ?_
where finally all_goals simp_all [Int.shiftLeft_eq, Int.pow_succ, ← Int.mul_assoc]

instance : Add Dyadic := ⟨Dyadic.add⟩

/-- Multiply two dyadic numbers. -/
protected def mul (x y : Dyadic) : Dyadic :=
  match x, y with
  | .zero, _ => .zero
  | _, .zero => .zero
  | .ofOdd n₁ k₁ hn₁, .ofOdd n₂ k₂ hn₂ =>
    .ofOdd (n₁ * n₂) (k₁ + k₂) (by rw [Int.mul_emod, hn₁, hn₂]; rfl)

instance : Mul Dyadic := ⟨Dyadic.mul⟩

/-- Negate a dyadic number. -/
protected def neg (x : Dyadic) : Dyadic :=
  match x with
  | .zero => .zero
  | .ofOdd n k hn => .ofOdd (-n) k (by rwa [Int.neg_emod_two])

instance : Neg Dyadic := ⟨Dyadic.neg⟩

/-- Subtract two dyadic numbers. -/
protected def sub (x y : Dyadic) : Dyadic := x + (- y)

instance : Sub Dyadic := ⟨Dyadic.sub⟩

/-- Shift a dyadic number left by `i` bits. -/
protected def shiftLeft (x : Dyadic) (i : Int) : Dyadic :=
  match x with
  | .zero => .zero
  | .ofOdd n k hn => .ofOdd n (k - i) hn

/-- Shift a dyadic number right by `i` bits. -/
protected def shiftRight (x : Dyadic) (i : Int) : Dyadic :=
  match x with
  | .zero => .zero
  | .ofOdd n k hn => .ofOdd n (k + i) hn

instance : HShiftLeft Dyadic Int Dyadic := ⟨Dyadic.shiftLeft⟩
instance : HShiftRight Dyadic Int Dyadic := ⟨Dyadic.shiftRight⟩

instance : HShiftLeft Dyadic Nat Dyadic := ⟨fun x y => x <<< (y : Int)⟩
instance : HShiftRight Dyadic Nat Dyadic := ⟨fun x y => x >>> (y : Int)⟩

-- TODO: move this
theorem _root_.Int.natAbs_emod_two (i : Int) : i.natAbs % 2 = (i % 2).natAbs := by omega

/-- Convert a dyadic number to a rational number. -/
def toRat (x : Dyadic) : Rat :=
  match x with
  | .zero => 0
  | .ofOdd n (k : Nat) hn =>
    have reduced : n.natAbs.Coprime (2 ^ k) := by
      apply Coprime.pow_right
      rw [coprime_iff_gcd_eq_one, Nat.gcd_comm, Nat.gcd_def]
      simp [hn, Int.natAbs_emod_two]
    ⟨n, 2 ^ k, Nat.ne_of_gt (Nat.pow_pos (by decide)), reduced⟩
  | .ofOdd n (-((k : Nat) + 1)) hn =>
    (n * (2 ^ (k + 1) : Nat) : Int)

@[simp] protected theorem zero_eq : Dyadic.zero = 0 := rfl
@[simp] protected theorem add_zero (x : Dyadic) : x + 0 = x := by cases x <;> rfl
@[simp] protected theorem zero_add (x : Dyadic) : 0 + x = x := by cases x <;> rfl
@[simp] protected theorem neg_zero : -0 = 0 := rfl
@[simp] protected theorem mul_zero (x : Dyadic) : x * 0 = 0 := by cases x <;> rfl
@[simp] protected theorem zero_mul (x : Dyadic) : 0 * x = 0 := by cases x <;> rfl

@[simp] theorem toRat_zero : toRat 0 = 0 := rfl

theorem _root_.Rat.mkRat_one (x : Int) : mkRat x 1 = x := by
  rw [← Rat.mk_den_one, Rat.mk_eq_mkRat]

theorem toRat_ofOdd_eq_mkRat :
    toRat (.ofOdd n k hn) = mkRat (n <<< (-k).toNat) (1 <<< k.toNat) := by
  cases k
  · simp [toRat, Rat.mk_eq_mkRat, Int.shiftLeft_eq, Nat.shiftLeft_eq]
  · simp [toRat, Int.neg_negSucc, Rat.mkRat_one, Int.shiftLeft_eq]

theorem toRat_ofIntWithPrec_eq_mkRat :
    toRat (.ofIntWithPrec n k) = mkRat (n <<< (-k).toNat) (1 <<< k.toNat) := by
  simp only [ofIntWithPrec]
  split
  · simp_all
  rw [toRat_ofOdd_eq_mkRat, Rat.mkRat_eq_iff (NeZero.ne _) (NeZero.ne _)]
  simp only [Int.natCast_shiftLeft, Int.cast_ofNat_Int, Int.shiftLeft_mul_shiftLeft, Int.mul_one]
  have : (-(k - n.trailingZeros) : Int).toNat + k.toNat =
      n.trailingZeros + ((-k).toNat + (k - n.trailingZeros).toNat) := by omega
  rw [this, Int.shiftLeft_add, Int.shiftRight_shiftLeft_cancel]
  exact Int.two_pow_trailingZeros_dvd ‹_›

example : ((3 : Dyadic) >>> 2) + ((3 : Dyadic) >>> 2) = ((3 : Dyadic) >>> 1) := rfl -- 3/4 + 3/4 = 3/2
example : ((7 : Dyadic) >>> 3) + ((1 : Dyadic) >>> 3) = 1 := rfl -- 7/8 + 1/8 = 1
example : (12 : Dyadic) + ((3 : Dyadic) >>> 1) = (27 : Dyadic) >>> 1 := rfl -- 12 + 3/2 = 27/2 = (2 * 13 + 1)/2^1
example : ((3 : Dyadic) >>> 1).add 12 =  (27 : Dyadic) >>> 1 := rfl -- 3/2 + 12 = 27/2 = (2 * 13 + 1)/2^1
example : (12 : Dyadic).add 12 = 24 := rfl -- 12 + 12 = 24

@[simp]
theorem toRat_add (x y : Dyadic) : toRat (x + y) = toRat x + toRat y := by
  match x, y with
  | .zero, _ => simp [toRat, Rat.zero_add]
  | _, .zero => simp [toRat, Rat.add_zero]
  | .ofOdd n₁ k₁ hn₁, .ofOdd n₂ k₂ hn₂ =>
    change (Dyadic.add _ _).toRat = _
    rw [Dyadic.add, toRat_ofOdd_eq_mkRat, toRat_ofOdd_eq_mkRat]
    rw [Rat.mkRat_add_mkRat _ _ (NeZero.ne _) (NeZero.ne _)]
    split
    · rename_i h
      cases Int.sub_eq_zero.mp h
      rw [toRat_ofIntWithPrec_eq_mkRat, Rat.mkRat_eq_iff (NeZero.ne _) (NeZero.ne _)]
      simp [Int.shiftLeft_mul_shiftLeft, Int.add_shiftLeft, Int.add_mul, Nat.add_assoc]
    · rename_i h
      cases Int.sub_eq_iff_eq_add.mp h
      rw [toRat_ofOdd_eq_mkRat, Rat.mkRat_eq_iff (NeZero.ne _) (NeZero.ne _)]
      simp only [succ_eq_add_one, Int.ofNat_eq_coe, Int.add_shiftLeft, ← Int.shiftLeft_add,
        Int.natCast_mul, Int.natCast_shiftLeft, Int.shiftLeft_mul_shiftLeft, Int.add_mul]
      congr 2 <;> omega
    · rename_i h
      cases Int.sub_eq_iff_eq_add.mp h
      rw [toRat_ofOdd_eq_mkRat, Rat.mkRat_eq_iff (NeZero.ne _) (NeZero.ne _)]
      simp only [Int.add_shiftLeft, ← Int.shiftLeft_add, Int.natCast_mul, Int.natCast_shiftLeft,
        Int.cast_ofNat_Int, Int.shiftLeft_mul_shiftLeft, Int.mul_one, Int.add_mul]
      congr 2 <;> omega

@[simp]
theorem toRat_neg (x : Dyadic) : toRat (-x) = - toRat x := by
  change x.neg.toRat = _
  cases x
  · rfl
  · simp [Dyadic.neg, Rat.neg_mkRat, Int.neg_shiftLeft, toRat_ofOdd_eq_mkRat]

@[simp]
theorem toRat_sub (x y : Dyadic) : toRat (x - y) = toRat x - toRat y := by
  change toRat (x + -y) = _
  simp [Rat.sub_eq_add_neg]

@[simp]
theorem toRat_mul (x y : Dyadic) : toRat (x * y) = toRat x * toRat y := by
  match x, y with
  | .zero, _ => simp
  | _, .zero => simp
  | .ofOdd n₁ k₁ hn₁, .ofOdd n₂ k₂ hn₂ =>
    change (Dyadic.mul _ _).toRat = _
    rw [Dyadic.mul, toRat_ofOdd_eq_mkRat, toRat_ofOdd_eq_mkRat, toRat_ofOdd_eq_mkRat,
      Rat.mkRat_mul_mkRat, Rat.mkRat_eq_iff (NeZero.ne _) (NeZero.ne _)]
    simp only [Int.natCast_mul, Int.natCast_shiftLeft, Int.cast_ofNat_Int,
      Int.shiftLeft_mul_shiftLeft, Int.mul_one]
    congr 1; omega

@[simp] theorem of_ne_zero : ofOdd n k hn ≠ 0 := Dyadic.noConfusion
@[simp] theorem zero_ne_of : 0 ≠ ofOdd n k hn := Dyadic.noConfusion

@[simp]
theorem toRat_eq_zero_iff {x : Dyadic} : x.toRat = 0 ↔ x = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  cases x
  · rfl
  · simp only [toRat_ofOdd_eq_mkRat, ne_eq, shiftLeft_eq_zero_iff, succ_ne_self, not_false_eq_true,
      Rat.mkRat_eq_zero, Int.shiftLeft_eq_zero_iff] at h
    cases h
    contradiction

theorem ofOdd_eq_ofIntWithPrec : ofOdd n k hn = ofIntWithPrec n k := by
  simp only [ofIntWithPrec, Dyadic.zero_eq, Int.trailingZeros_eq_zero_of_mod_eq hn,
    Int.shiftRight_zero, Int.cast_ofNat_Int, Int.sub_zero, right_eq_dite_iff, of_ne_zero, imp_false]
  intro rfl; contradiction

@[simp]
theorem ofIntWithPrec_zero {i : Int} : ofIntWithPrec 0 i = 0 := rfl

theorem ofIntWithPrec_shiftLeft_add {n : Nat} :
    ofIntWithPrec ((x : Int) <<< n) (i + n) = ofIntWithPrec x i := by
  rw [ofIntWithPrec, ofIntWithPrec]
  simp only [Int.shiftLeft_eq_zero_iff]
  split
  · rfl
  · simp [Int.trailingZeros_shiftLeft, *, Int.shiftLeft_shiftRight_eq_shiftRight_of_le,
      Int.add_comm x.trailingZeros n, ← Int.sub_sub]

/-- The "precision" of a dyadic number, i.e. in `n * 2^(-p)` with `n` odd the precision is `p`. -/
def precision : Dyadic → Int
  | .zero => 0
  | .ofOdd _ p _ => p

/--
Convert a rational number `x` to the greatest dyadic number with precision at most `prec`
which is less than or equal to `x`.
-/
def _root_.Rat.toDyadic (x : Rat) (prec : Int) : Dyadic :=
  match prec with
  | (n : Nat) => .ofIntWithPrec ((x.num <<< n) / x.den) prec
  | -(n + 1 : Nat) => .ofIntWithPrec (x.num / (x.den <<< (n + 1))) prec

theorem _root_.Rat.toDyadic_mkRat (a : Int) (b : Nat) (prec : Int) :
    Rat.toDyadic (mkRat a b) prec =
      .ofIntWithPrec ((a <<< prec.toNat) / (b <<< (-prec).toNat)) prec := by
  by_cases hb : b = 0
  · cases prec <;> simp [hb, Rat.toDyadic]
  rcases h : mkRat a b with ⟨n, d, hnz, hr⟩
  obtain ⟨m, hm, rfl, rfl⟩ := Rat.mkRat_num_den hb h
  cases prec
  · simp only [Rat.toDyadic, Int.ofNat_eq_coe, Int.toNat_natCast, Int.toNat_neg_nat,
      shiftLeft_zero, Int.natCast_mul]
    rw [Int.mul_comm d, ← Int.ediv_ediv (by simp), ← Int.shiftLeft_mul,
      Int.mul_ediv_cancel _ (by simpa using hm)]
  · simp only [Rat.toDyadic, Int.natCast_shiftLeft, Int.negSucc_eq, ← Int.natCast_add_one,
      Int.toNat_neg_nat, Int.shiftLeft_zero, Int.neg_neg, Int.toNat_natCast, Int.natCast_mul]
    rw [Int.mul_comm d, ← Int.mul_shiftLeft, ← Int.ediv_ediv (by simp),
      Int.mul_ediv_cancel _ (by simpa using hm)]

/--
Rounds a dyadic rational `x` down to the greatest dyadic number with precision at most `prec`
which is less than or equal to `x`.
-/
def roundDown (x : Dyadic) (prec : Int) : Dyadic :=
  match x with
  | .zero => .zero
  | .ofOdd n k _ =>
    match k - prec with
    | .ofNat l => .ofIntWithPrec (n >>> l) prec
    | .negSucc _ => x

theorem roundDown_eq_self_of_le {x : Dyadic} {prec : Int} (h : x.precision ≤ prec) :
    roundDown x prec = x := by
  rcases x with _ | ⟨n, k, hn⟩
  · rfl
  · simp only [precision] at h
    obtain ⟨a, rfl⟩ := h.dest
    rcases a with _ | a
    · simp [roundDown, ofOdd_eq_ofIntWithPrec]
    · have : k - (k + (a + 1 : Nat)) = Int.negSucc a := by omega
      simp only [roundDown, this]

@[simp]
theorem toDyadic_toRat (x : Dyadic) (prec : Int) :
    x.toRat.toDyadic prec = x.roundDown prec := by
  rcases x with _ | ⟨n, k, hn⟩
  · cases prec <;> simp [Rat.toDyadic, roundDown]
  · simp only [toRat_ofOdd_eq_mkRat, roundDown]
    rw [Rat.toDyadic_mkRat]
    simp only [← Int.shiftLeft_add, Int.natCast_shiftLeft, Int.cast_ofNat_Int]
    rw [Int.shiftLeft_eq' 1, Int.one_mul, ← Int.shiftRight_eq_div_pow]
    rw [Int.shiftLeft_shiftRight_eq, ← Int.toNat_sub, ← Int.toNat_sub, ← Int.neg_sub]
    have : ((k.toNat + (-prec).toNat : Nat) - ((-k).toNat + prec.toNat : Nat) : Int) = k - prec := by
      omega
    rw [this]
    cases h : k - prec
    · simp
    · simp
      rw [Int.negSucc_eq, Int.eq_neg_comm, Int.neg_sub, eq_comm, Int.sub_eq_iff_eq_add] at h
      simp only [Int.neg_negSucc, h, ← Int.natCast_add_one, Int.add_comm _ k,
        Nat.succ_eq_add_one, Int.toNat_natCast, ofIntWithPrec_shiftLeft_add, ofOdd_eq_ofIntWithPrec]

theorem toRat_inj {x y : Dyadic} : x.toRat = y.toRat ↔ x = y := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  cases x <;> cases y
  · rfl
  · simp [eq_comm (a := (0 : Rat))] at h
  · simp at h
  · rename_i n₁ k₁ hn₁ n₂ k₂ hn₂
    replace h := congrArg (·.toDyadic (max k₁ k₂)) h
    simpa [toDyadic_toRat, roundDown_eq_self_of_le, precision, Int.le_max_left, Int.le_max_right]
      using h

theorem add_comm (x y : Dyadic) : x + y = y + x := by
  rw [← toRat_inj, toRat_add, toRat_add]
  sorry
theorem add_assoc (x y z : Dyadic) : (x + y) + z = x + (y + z) := by
  rw [← toRat_inj, toRat_add, toRat_add, toRat_add, toRat_add]
  sorry
theorem mul_comm (x y : Dyadic) : x * y = y * x := by
  rw [← toRat_inj, toRat_mul, toRat_mul]
  sorry
theorem mul_assoc (x y z : Dyadic) : (x * y) * z = x * (y * z) := by
  rw [← toRat_inj, toRat_mul, toRat_mul, toRat_mul, toRat_mul]
  sorry
theorem mul_one (x : Dyadic) : x * 1 = x := by
  rw [← toRat_inj, toRat_mul]
  sorry
theorem one_mul (x : Dyadic) : 1 * x = x := by
  rw [← toRat_inj, toRat_mul]
  sorry

-- etc, then construct a `Lean.Grind.CommRing` instance

/-- Determine if a dyadic rational is strictly less than another. -/
def blt (x y : Dyadic) : Bool :=
  match x, y with
  | .zero, .zero => false
  | .zero, .ofOdd n₂ _ _ => 0 < n₂
  | .ofOdd n₁ _ _, .zero => n₁ < 0
  | .ofOdd n₁ k₁ _, .ofOdd n₂ k₂ _ =>
    match k₂ - k₁ with
    | (l : Nat) => (n₁ <<< l) < n₂
    | -((l+1 : Nat)) => n₁ < (n₂ <<< l + 1)

/-- Determine if a dyadic rational is less than or equal to another. -/
def ble (x y : Dyadic) : Bool :=
  match x, y with
  | .zero, .zero => true
  | .zero, .ofOdd n₂ _ _ => 0 ≤ n₂
  | .ofOdd n₁ _ _, .zero => n₁ ≤ 0
  | .ofOdd n₁ k₁ _, .ofOdd n₂ k₂ _ =>
    match k₂ - k₁ with
    | (l : Nat) => (n₁ <<< l) ≤ n₂
    | -((l+1 : Nat)) => n₁ ≤ (n₂ <<< l + 1)

theorem blt_iff_toRat : blt x y ↔ x.toRat < y.toRat := sorry
theorem ble_iff_toRat : ble x y ↔ x.toRat ≤ y.toRat := sorry

instance : LT Dyadic where
  lt x y := blt x y

instance : LE Dyadic where
  le x y := ble x y

theorem lt_iff_toRat {x y : Dyadic} : x < y ↔ x.toRat < y.toRat := by
  rw [← blt_iff_toRat]
  exact Iff.rfl
theorem le_iff_toRat {x y : Dyadic} : x ≤ y ↔ x.toRat ≤ y.toRat := by
  rw [← ble_iff_toRat]
  exact Iff.rfl

theorem lt_iff (x y : Dyadic) : x < y ↔ x ≤ y ∧ ¬y ≤ x := sorry

theorem le_refl (x : Dyadic) : x ≤ x := by
  rw [le_iff_toRat]
  -- We can't yet prove theorems about the order by pulling back from `Rat`,
  -- because we don't have the order instances there!
  sorry

theorem le_trans (x y z : Dyadic) (h : x ≤ y) (h' : y ≤ z) : x ≤ z := by
  rw [le_iff_toRat] at h h'
  sorry

theorem le_antisymm (x y : Dyadic) (h : x ≤ y) (h' : y ≤ x) : x = y := by
  rw [le_iff_toRat] at h h'
  sorry

theorem le_total (x y : Dyadic) : x ≤ y ∨ y ≤ x := sorry

instance : Std.LawfulOrderLT Dyadic where
  lt_iff := lt_iff

instance : Std.IsPreorder Dyadic where
  le_refl := le_refl
  le_trans := le_trans

instance : Std.IsPartialOrder Dyadic where
  le_antisymm := le_antisymm

instance : Std.IsLinearPreorder Dyadic where
  le_total := le_total

instance : Std.IsLinearOrder Dyadic where

theorem roundDown_le {x : Dyadic} {prec : Int} : roundDown x prec ≤ x :=
  match x with
  | .zero => le_refl _
  | .ofOdd n k _ => by
    unfold roundDown
    dsimp
    split
    · sorry
    · apply le_refl

theorem precision_roundDown {x : Dyadic} {prec : Int} : (roundDown x prec).precision ≤ prec := sorry

theorem le_roundDown {x y : Dyadic} {prec : Int} (h : y.precision ≤ prec) (h' : y ≤ x) : y ≤ x.roundDown prec := sorry

/-- `roundUp x prec` is the least dyadic number with precision at most `prec` which is greater than or equal to `x`. -/
def roundUp (x : Dyadic) (prec : Int) : Dyadic :=
  match x with
  | .zero => .zero
  | .ofOdd n k _ =>
    match k - prec with
    | .ofNat l => .ofIntWithPrec (n + 1 >>> l) prec
    | .negSucc _ => x

theorem le_roundUp {x : Dyadic} {prec : Int} : x ≤ roundUp x prec :=
  match x with
  | .zero => le_refl _
  | .ofOdd n k _ => by
    unfold roundUp
    dsimp
    split
    · sorry
    · apply le_refl

theorem precision_roundUp {x : Dyadic} {prec : Int} : (roundUp x prec).precision ≤ prec := sorry

theorem roundUp_le {x y : Dyadic} {prec : Int} (h : y.precision ≤ prec) (h' : x ≤ y) : x.roundUp prec ≤ y:= sorry

end Dyadic
