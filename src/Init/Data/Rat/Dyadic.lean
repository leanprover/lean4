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

-- TODO replace all `· * 2 ^ k` with `· <<< k` (in definitions)

set_option linter.missingDocs true

@[expose] public section

open Nat

namespace Int

-- TODO: move these instances, or make them local to this file.
instance [NeZero n] : NeZero ((n : Int) ^ m) := ⟨Int.pow_ne_zero (NeZero.ne _)⟩
instance [NeZero (n : Nat)] : NeZero (n : Int) := ⟨mt Int.natCast_eq_zero.mp (NeZero.ne _)⟩
instance [NeZero (n : Nat)] : NeZero (no_index (OfNat.ofNat n : Int)) := ⟨mt Int.natCast_eq_zero.mp (NeZero.ne _)⟩

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

theorem trailingZeros_two_pow_mul {x : Int} (hx : x ≠ 0) (n : Nat) :
    trailingZeros (2 ^ n * x) = x.trailingZeros + n := by
  have (a : Nat) : 2 ^ a * x ≠ 0 := Int.mul_ne_zero (Int.pow_ne_zero (by decide)) hx
  induction n <;> simp [Int.pow_succ', Int.mul_assoc, trailingZeros_two_mul (this _), *,
    Nat.add_assoc]

end Int

/--
A dyadic rational is either zero or of the form `n * 2^(-k)` for some (unique) `n k : Int`
where `n` is odd.
-/
inductive Dyadic where
  | zero
  | of (n : Int) (k : Int) (hn : n % 2 = 1)
deriving DecidableEq

/-- Returns the dyadic number representation of `i * 2 ^ (-exp)`. -/
def Dyadic.ofIntWithPrec (i : Int) (prec : Int) : Dyadic :=
  if h : i = 0 then .zero
  else .of (i >>> i.trailingZeros) (prec - i.trailingZeros) (Int.shiftRight_trailingZeros_mod_two h)

def Dyadic.ofInt (i : Int) : Dyadic :=
  Dyadic.ofIntWithPrec i 0

namespace Dyadic

instance (n : Nat) : OfNat Dyadic n where
  ofNat := Dyadic.ofInt n

protected def add (x y : Dyadic) : Dyadic :=
  match x, y with
  | .zero, y => y
  | x, .zero => x
  | .of n₁ k₁ hn₁, .of n₂ k₂ hn₂ =>
    match k₁ - k₂ with
    | 0 => .ofIntWithPrec (n₁ + n₂) k₁
    | (d@hd:(d' + 1) : Nat) => .of (n₁ + (n₂ <<< d)) k₁ ?_
    | -(d + 1 : Nat) => .of (n₁ <<< (d + 1) + n₂) k₂ ?_
where finally all_goals simp_all [Int.shiftLeft_eq, Int.pow_succ, ← Int.mul_assoc]

instance : Add Dyadic := ⟨Dyadic.add⟩

protected def mul (x y : Dyadic) : Dyadic :=
  match x, y with
  | .zero, _ => .zero
  | _, .zero => .zero
  | .of n₁ k₁ hn₁, .of n₂ k₂ hn₂ =>
    .of (n₁ * n₂) (k₁ + k₂) (by rw [Int.mul_emod, hn₁, hn₂]; rfl)

instance : Mul Dyadic := ⟨Dyadic.mul⟩

protected def neg (x : Dyadic) : Dyadic :=
  match x with
  | .zero => .zero
  | .of n k hn => .of (-n) k (by rwa [Int.neg_emod_two])

instance : Neg Dyadic := ⟨Dyadic.neg⟩

protected def sub (x y : Dyadic) : Dyadic := x + (- y)

instance : Sub Dyadic := ⟨Dyadic.sub⟩

protected def shiftLeft (x : Dyadic) (i : Int) : Dyadic :=
  match x with
  | .zero => .zero
  | .of n k hn => .of n (k - i) hn

protected def shiftRight (x : Dyadic) (i : Int) : Dyadic :=
  match x with
  | .zero => .zero
  | .of n k hn => .of n (k + i) hn

instance : HShiftLeft Dyadic Int Dyadic := ⟨Dyadic.shiftLeft⟩
instance : HShiftRight Dyadic Int Dyadic := ⟨Dyadic.shiftRight⟩

instance : HShiftLeft Dyadic Nat Dyadic := ⟨fun x y => x <<< (y : Int)⟩
instance : HShiftRight Dyadic Nat Dyadic := ⟨fun x y => x >>> (y : Int)⟩

-- TODO: move this
theorem _root_.Int.natAbs_emod_two (i : Int) : i.natAbs % 2 = (i % 2).natAbs := by omega

def toRat (x : Dyadic) : Rat :=
  match x with
  | .zero => 0
  | .of n (k : Nat) hn =>
    have reduced : n.natAbs.Coprime (2 ^ k) := by
      apply Coprime.pow_right
      rw [coprime_iff_gcd_eq_one, Nat.gcd_comm, Nat.gcd_def]
      simp [hn, Int.natAbs_emod_two]
    ⟨n, 2 ^ k, Nat.ne_of_gt (Nat.pow_pos (by decide)), reduced⟩
  | .of n (-((k : Nat) + 1)) hn =>
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

theorem toRat_of_eq_mkRat :
    toRat (.of n k hn) = mkRat (n * (2 ^ (-k).toNat : Nat)) (2 ^ k.toNat : Nat) := by
  cases k
  · simp [toRat, Rat.mk_eq_mkRat]
  · simp [toRat, Int.neg_negSucc, Rat.mkRat_one]

theorem toRat_ofIntWithPrec_eq_mkRat :
    toRat (.ofIntWithPrec n k) = mkRat (n * (2 ^ (-k).toNat : Nat)) (2 ^ k.toNat : Nat) := by
  simp only [ofIntWithPrec]
  split
  · simp_all
  rw [toRat_of_eq_mkRat, Rat.mkRat_eq_iff (NeZero.ne _) (NeZero.ne _)]
  simp only [Int.mul_assoc, ← Int.natCast_mul, ← Nat.pow_add]
  have : (-(k - n.trailingZeros) : Int).toNat + k.toNat =
      n.trailingZeros + ((-k).toNat + (k - n.trailingZeros).toNat) := by omega
  rw [this, Nat.pow_add, Int.natCast_mul, ← Int.mul_assoc, Int.shiftRight_eq_div_pow,
    Int.ediv_mul_cancel]
  rw [Int.natCast_pow]
  exact Int.two_pow_trailingZeros_dvd ‹_›

example : ((3 : Dyadic) >>> 2).add ((3 : Dyadic) >>> 2) = ((3 : Dyadic) >>> 1) := rfl -- 3/4 + 3/4 = 3/2
example : ((7 : Dyadic) >>> 3).add ((1 : Dyadic) >>> 3) = 1 := rfl -- 7/8 + 1/8 = 1
example : (12 : Dyadic).add ((3 : Dyadic) >>> 1) = (27 : Dyadic) >>> 1 := rfl -- 12 + 3/2 = 27/2 = (2 * 13 + 1)/2^1
example : ((3 : Dyadic) >>> 1).add 12 =  (27 : Dyadic) >>> 1 := rfl -- 3/2 + 12 = 27/2 = (2 * 13 + 1)/2^1
example : (12 : Dyadic).add 12 = 24 := rfl -- 12 + 12 = 24

@[simp]
theorem toRat_add (x y : Dyadic) : toRat (x + y) = toRat x + toRat y := by
  match x, y with
  | .zero, _ => simp [toRat, Rat.zero_add]
  | _, .zero => simp [toRat, Rat.add_zero]
  | .of n₁ k₁ hn₁, .of n₂ k₂ hn₂ =>
    change (Dyadic.add _ _).toRat = _
    rw [Dyadic.add, toRat_of_eq_mkRat, toRat_of_eq_mkRat]
    rw [Rat.mkRat_add_mkRat _ _ (NeZero.ne _) (NeZero.ne _)]
    split
    · rename_i h
      cases Int.sub_eq_zero.mp h
      rw [toRat_ofIntWithPrec_eq_mkRat, Rat.mkRat_eq_iff (NeZero.ne _) (NeZero.ne _)]
      simp [Int.add_mul, Int.mul_assoc]
    · rename_i h
      cases Int.sub_eq_iff_eq_add.mp h
      rw [toRat_of_eq_mkRat, Rat.mkRat_eq_iff (NeZero.ne _) (NeZero.ne _)]
      simp only [Int.shiftLeft_eq', Int.add_mul, Int.mul_assoc, ← Int.natCast_mul, ← Nat.pow_add,
        Int.ofNat_eq_coe]
      congr 4 <;> omega
    · rename_i h
      cases Int.sub_eq_iff_eq_add.mp h
      rw [toRat_of_eq_mkRat, Rat.mkRat_eq_iff (NeZero.ne _) (NeZero.ne _)]
      simp only [Int.shiftLeft_eq', Int.add_mul, Int.mul_assoc, ← Int.natCast_mul, ← Nat.pow_add]
      congr 4 <;> omega

@[simp]
theorem toRat_neg (x : Dyadic) : toRat (-x) = - toRat x := by
  change x.neg.toRat = _
  cases x
  · rfl
  · simp [Dyadic.neg, Rat.neg_mkRat, Int.neg_mul, toRat_of_eq_mkRat]

@[simp]
theorem toRat_sub (x y : Dyadic) : toRat (x - y) = toRat x - toRat y := by
  change toRat (x + -y) = _
  simp [Rat.sub_eq_add_neg]

@[simp]
theorem toRat_mul (x y : Dyadic) : toRat (x * y) = toRat x * toRat y := by
  match x, y with
  | .zero, _ => simp
  | _, .zero => simp
  | .of n₁ k₁ hn₁, .of n₂ k₂ hn₂ =>
    change (Dyadic.mul _ _).toRat = _
    rw [Dyadic.mul, toRat_of_eq_mkRat, toRat_of_eq_mkRat, toRat_of_eq_mkRat, Rat.mkRat_mul_mkRat,
      Rat.mkRat_eq_iff (NeZero.ne _) (NeZero.ne _)]
    simp only [Int.mul_assoc, ← Int.natCast_mul, ← Nat.pow_add, Int.mul_left_comm _ n₂]
    congr 4; omega

@[simp] theorem of_ne_zero : of n k hn ≠ 0 := Dyadic.noConfusion
@[simp] theorem zero_ne_of : 0 ≠ of n k hn := Dyadic.noConfusion

@[simp]
theorem toRat_eq_zero_iff {x : Dyadic} : x.toRat = 0 ↔ x = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  cases x
  · rfl
  · simp only [toRat_of_eq_mkRat, ne_eq, NeZero.ne, not_false_eq_true, Rat.mkRat_eq_zero,
      Int.mul_eq_zero, or_false] at h
    cases h
    contradiction

def precision : Dyadic → Int
  | .zero => 0
  | .of _ p _ => p

def _root_.Rat.toDyadic (x : Rat) (prec : Int) : Dyadic :=
  match prec with
  | (n : Nat) => .ofIntWithPrec ((x.num <<< n) / x.den) prec
  | -(n + 1 : Nat) => .ofIntWithPrec (x.num / (x.den <<< (n + 1))) prec

theorem of_eq_ofIntWithPrec : of n k hn = ofIntWithPrec n k := by
  simp only [ofIntWithPrec, Dyadic.zero_eq, Int.trailingZeros_eq_zero_of_mod_eq hn,
    Int.shiftRight_zero, Int.cast_ofNat_Int, Int.sub_zero, right_eq_dite_iff, of_ne_zero, imp_false]
  intro rfl; contradiction

theorem ofIntWithPrec_two_pow_mul_add {n : Nat} :
    ofIntWithPrec (2 ^ n * x) (i + n) = ofIntWithPrec x i := by
  rw [ofIntWithPrec, ofIntWithPrec]
  simp only [Int.mul_eq_zero, ne_eq, Int.reduceEq, not_false_eq_true, Int.pow_ne_zero, false_or,
    Dyadic.zero_eq]
  split
  · rfl
  · simp only [ne_eq, not_false_eq_true, Int.trailingZeros_two_pow_mul, Nat.add_comm _ n,
      Int.shiftRight_add, of.injEq, *]
    rw [Int.shiftRight_eq_div_pow _ n, Int.natCast_pow, Int.cast_ofNat_Int,
      Int.mul_ediv_cancel_left _ (NeZero.ne _)]
    simp [← Int.sub_sub]

theorem toDyadic_toRat {x : Dyadic} {prec : Int} (h : x.precision ≤ prec) :
    x.toRat.toDyadic prec = x := by
  rcases x with _ | ⟨n, k, hn⟩
  · simp only [precision] at h
    rcases h.dest with ⟨a, rfl⟩
    simp [Rat.toDyadic, ofIntWithPrec, Int.shiftLeft_eq']
  · simp only [precision] at h
    rcases h.dest with ⟨a, rfl⟩
    rcases k with b | b
    · simp only [toRat, Rat.toDyadic, Int.ofNat_eq_coe, ← Int.natCast_add, Nat.pow_add,
        Int.natCast_mul, Int.shiftLeft_eq']
      rw [Int.mul_comm, Int.mul_assoc, Int.mul_ediv_cancel_left _ (NeZero.ne _)]
      rw [Int.natCast_pow, Int.cast_ofNat_Int, Int.natCast_add, ofIntWithPrec_two_pow_mul_add]
      rw [of_eq_ofIntWithPrec]
    · simp only [toRat, Rat.toDyadic]
      split
      · simp only [← Rat.mk_den_one, Int.cast_ofNat_Int, Int.ediv_one]
        rename_i c h
        rw [Int.negSucc_eq, Int.add_comm, Int.add_neg_eq_sub, Int.sub_eq_iff_eq_add',
          Int.ofNat_eq_coe] at h
        norm_cast at h
        simp only [Int.shiftLeft_eq', Int.mul_assoc, ← Int.natCast_mul, ← Nat.pow_add, h]
        rw [Int.natCast_pow, Int.cast_ofNat_Int, Int.mul_comm]
        rw [ofIntWithPrec_two_pow_mul_add, of_eq_ofIntWithPrec]
      · simp only [← Rat.mk_den_one, Nat.shiftLeft_eq, Nat.one_mul]
        rename_i c h
        have : b = a + c := by omega
        cases this
        rw [Nat.add_assoc, Nat.pow_add, Int.natCast_mul, ← Int.mul_assoc,
          Int.mul_ediv_cancel _ (NeZero.ne _), Int.mul_comm, Int.natCast_pow,
          Int.cast_ofNat_Int, ofIntWithPrec_two_pow_mul_add, of_eq_ofIntWithPrec]

theorem toRat_inj {x y : Dyadic} : x.toRat = y.toRat ↔ x = y := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  cases x <;> cases y
  · rfl
  · simp [eq_comm (a := (0 : Rat))] at h
  · simp at h
  · rename_i n₁ k₁ hn₁ n₂ k₂ hn₂
    replace h := congrArg (·.toDyadic (max k₁ k₂)) h
    simpa [toDyadic_toRat, precision, Int.le_max_left, Int.le_max_right] using h

-- TODO: Define `roundUp : (x : Dyadic) → (prec : Int) → Dyadic` as the closest dyadic ≥ `x` with precision is at most `prec`, and theorems about this. Similarly `roundDown`.

-- TODO: Prove the ring axioms via injectivity of `toRat`, and construct a `Lean.Grind.CommRing` instance.

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

-- etc

/-- Determine if a dyadic rational is strictly less than another. -/
def blt (x y : Dyadic) : Bool :=
  match x, y with
  | .zero, .zero => false
  | .zero, .of n₂ _ _ => 0 < n₂
  | .of n₁ _ _, .zero => n₁ < 0
  | .of n₁ k₁ _, .of n₂ k₂ _ =>
    match k₂ - k₁ with
    | (l : Nat) => (n₁ <<< l) < n₂
    | -((l+1 : Nat)) => n₁ < (n₂ <<< l + 1)

/-- Determine if a dyadic rational is less than or equal to another. -/
def ble (x y : Dyadic) : Bool :=
  match x, y with
  | .zero, .zero => true
  | .zero, .of n₂ _ _ => 0 ≤ n₂
  | .of n₁ _ _, .zero => n₁ ≤ 0
  | .of n₁ k₁ _, .of n₂ k₂ _ =>
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

instance : Std.LawfulOrderLT Dyadic where
  lt_iff := sorry

instance : Std.IsPartialOrder Dyadic where
  le_refl x := by
    rw [le_iff_toRat]
    -- Oops, can't do this yet because we don't have the order instances on `Rat` itself
    sorry
  le_trans := by sorry
  le_antisymm := by sorry

instance : Std.IsLinearPreorder Dyadic where
  le_total := by sorry

instance : Std.IsLinearOrder Dyadic where

-- TODO: show Dyadic is an IsOrderedRing

end Dyadic
