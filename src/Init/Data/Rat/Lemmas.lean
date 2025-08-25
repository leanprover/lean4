/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl, Robin Arnez
-/
module
prelude

public import Init.Data.Rat.Basic
import Init.Data.Int.Bitwise.Lemmas

@[expose] public section

/-! # Lemmas about the Rational Numbers -/

namespace Rat

-- This is not marked as an `@[ext]` lemma as this is rarely useful for rational numbers.
theorem ext : {p q : Rat} → p.num = q.num → p.den = q.den → p = q
  | ⟨_,_,_,_⟩, ⟨_,_,_,_⟩, rfl, rfl => rfl

@[simp] theorem mk_den_one {r : Int} :
    ⟨r, 1, Nat.one_ne_zero, (Nat.coprime_one_right _)⟩ = (r : Rat) := rfl

@[simp] theorem zero_num : (0 : Rat).num = 0 := rfl
@[simp] theorem zero_den : (0 : Rat).den = 1 := rfl
@[simp] theorem one_num : (1 : Rat).num = 1 := rfl
@[simp] theorem one_den : (1 : Rat).den = 1 := rfl

@[simp] theorem maybeNormalize_eq {num den g} (dvd_num dvd_den den_nz reduced) :
    maybeNormalize num den g dvd_num dvd_den den_nz reduced =
    { num := num.divExact g dvd_num, den := den / g, den_nz, reduced } := by
  unfold maybeNormalize; split
  · subst g; simp
  · rfl

theorem normalize_eq {num den} (den_nz) : normalize num den den_nz =
    { num := num / num.natAbs.gcd den
      den := den / num.natAbs.gcd den
      den_nz := normalize.den_nz den_nz rfl
      reduced := normalize.reduced den_nz rfl } := by
  simp only [normalize, maybeNormalize_eq, Int.divExact_eq_ediv]

@[simp] theorem normalize_zero (nz) : normalize 0 d nz = 0 := by
  simp [normalize, Int.natAbs_zero, Nat.div_self (Nat.pos_of_ne_zero nz)]; rfl

theorem mk_eq_normalize (num den nz c) : ⟨num, den, nz, c⟩ = normalize num den nz := by
  simp [normalize_eq, c.gcd_eq_one]

theorem normalize_eq_mk' (n : Int) (d : Nat) (h : d ≠ 0) (c : Nat.gcd (Int.natAbs n) d = 1) :
    normalize n d h = mk' n d h c := (mk_eq_normalize ..).symm

theorem normalize_self (r : Rat) : normalize r.num r.den r.den_nz = r := (mk_eq_normalize ..).symm

theorem normalize_mul_left {a : Nat} (d0 : d ≠ 0) (a0 : a ≠ 0) :
    normalize (↑a * n) (a * d) (Nat.mul_ne_zero a0 d0) = normalize n d d0 := by
  simp [normalize_eq, Int.natAbs_mul, Nat.gcd_mul_left,
    Nat.mul_div_mul_left _ _ (Nat.pos_of_ne_zero a0), Int.natCast_mul,
    Int.mul_ediv_mul_of_pos _ _ (Int.natCast_pos.2 <| Nat.pos_of_ne_zero a0)]

theorem normalize_mul_right {a : Nat} (d0 : d ≠ 0) (a0 : a ≠ 0) :
    normalize (n * a) (d * a) (Nat.mul_ne_zero d0 a0) = normalize n d d0 := by
  rw [← normalize_mul_left (d0 := d0) a0]
  congr 1
  · apply Int.mul_comm
  · apply Nat.mul_comm

theorem normalize_eq_iff (z₁ : d₁ ≠ 0) (z₂ : d₂ ≠ 0) :
    normalize n₁ d₁ z₁ = normalize n₂ d₂ z₂ ↔ n₁ * d₂ = n₂ * d₁ := by
  constructor <;> intro h
  · simp only [normalize_eq, mk'.injEq] at h
    have hn₁ := Int.ofNat_dvd_left.2 <| Nat.gcd_dvd_left n₁.natAbs d₁
    have hn₂ := Int.ofNat_dvd_left.2 <| Nat.gcd_dvd_left n₂.natAbs d₂
    have hd₁ := Int.ofNat_dvd.2 <| Nat.gcd_dvd_right n₁.natAbs d₁
    have hd₂ := Int.ofNat_dvd.2 <| Nat.gcd_dvd_right n₂.natAbs d₂
    rw [← Int.ediv_mul_cancel (Int.dvd_trans hd₂ (Int.dvd_mul_left ..)),
      Int.mul_ediv_assoc _ hd₂, ← Int.natCast_ediv, ← h.2, Int.natCast_ediv,
      ← Int.mul_ediv_assoc _ hd₁, Int.mul_ediv_assoc' _ hn₁,
      Int.mul_right_comm, h.1, Int.ediv_mul_cancel hn₂]
  · rw [← normalize_mul_right _ z₂, ← normalize_mul_left z₂ z₁, Int.mul_comm d₁, h]

theorem maybeNormalize_eq_normalize {num : Int} {den g : Nat} (dvd_num dvd_den den_nz reduced)
    (hn : ↑g ∣ num) (hd : g ∣ den) :
    maybeNormalize num den g dvd_num dvd_den den_nz reduced =
      normalize num den (mt (by simp [·]) den_nz) := by
  simp only [maybeNormalize_eq, mk_eq_normalize, Int.divExact_eq_ediv]
  have : g ≠ 0 := mt (by simp [·]) den_nz
  rw [← normalize_mul_right _ this, Int.ediv_mul_cancel hn]
  congr 1; exact Nat.div_mul_cancel hd

@[simp] theorem normalize_eq_zero (d0 : d ≠ 0) : normalize n d d0 = 0 ↔ n = 0 := by
  have' := normalize_eq_iff d0 Nat.one_ne_zero
  rw [normalize_zero (d := 1)] at this; rw [this]; simp

theorem normalize_num_den' (num den nz) : ∃ d : Nat, d ≠ 0 ∧
    num = (normalize num den nz).num * d ∧ den = (normalize num den nz).den * d := by
  refine ⟨num.natAbs.gcd den, Nat.gcd_ne_zero_right nz, ?_⟩
  simp [normalize_eq, Int.ediv_mul_cancel (Int.ofNat_dvd_left.2 <| Nat.gcd_dvd_left ..),
    Nat.div_mul_cancel (Nat.gcd_dvd_right ..)]

theorem normalize_num_den (h : normalize n d z = ⟨n', d', z', c⟩) :
    ∃ m : Nat, m ≠ 0 ∧ n = n' * m ∧ d = d' * m := by
  have := normalize_num_den' n d z; rwa [h] at this

theorem normalize_eq_mkRat {num den} (den_nz) : normalize num den den_nz = mkRat num den := by
  simp [mkRat, den_nz]

theorem mkRat_num_den (z : d ≠ 0) (h : mkRat n d = ⟨n', d', z', c⟩) :
    ∃ m : Nat, m ≠ 0 ∧ n = n' * m ∧ d = d' * m :=
  normalize_num_den ((normalize_eq_mkRat z).symm ▸ h)

theorem mkRat_def (n d) : mkRat n d = if d0 : d = 0 then 0 else normalize n d d0 := rfl

@[simp]
theorem mkRat_self (a : Rat) : mkRat a.num a.den = a := by
  rw [← normalize_eq_mkRat a.den_nz, normalize_self]

theorem mk_eq_mkRat (num den nz c) : ⟨num, den, nz, c⟩ = mkRat num den := by
  simp [mk_eq_normalize, normalize_eq_mkRat]

@[simp] theorem zero_mkRat (n) : mkRat 0 n = 0 := by simp [mkRat_def]

@[simp] theorem mkRat_zero (n) : mkRat n 0 = 0 := by simp [mkRat_def]

theorem mkRat_eq_zero (d0 : d ≠ 0) : mkRat n d = 0 ↔ n = 0 := by simp [mkRat_def, d0]

theorem mkRat_ne_zero (d0 : d ≠ 0) : mkRat n d ≠ 0 ↔ n ≠ 0 := not_congr (mkRat_eq_zero d0)

theorem mkRat_mul_left {a : Nat} (a0 : a ≠ 0) : mkRat (↑a * n) (a * d) = mkRat n d := by
  if d0 : d = 0 then simp [d0] else
  rw [← normalize_eq_mkRat d0, ← normalize_mul_left d0 a0, normalize_eq_mkRat]

theorem mkRat_mul_right {a : Nat} (a0 : a ≠ 0) : mkRat (n * a) (d * a) = mkRat n d := by
  rw [← mkRat_mul_left (d := d) a0]
  congr 1
  · apply Int.mul_comm
  · apply Nat.mul_comm

theorem mkRat_eq_iff (z₁ : d₁ ≠ 0) (z₂ : d₂ ≠ 0) :
    mkRat n₁ d₁ = mkRat n₂ d₂ ↔ n₁ * d₂ = n₂ * d₁ := by
  rw [← normalize_eq_mkRat z₁, ← normalize_eq_mkRat z₂, normalize_eq_iff]

@[simp] theorem divInt_ofNat (num den) : num /. (den : Nat) = mkRat num den := by
  simp [divInt]

theorem mk_eq_divInt (num den nz c) : ⟨num, den, nz, c⟩ = num /. (den : Nat) := by
  simp [mk_eq_mkRat]

theorem num_divInt_den (a : Rat) : a.num /. a.den = a := by rw [divInt_ofNat, mkRat_self]

theorem mk'_eq_divInt {n d h c} : (⟨n, d, h, c⟩ : Rat) = n /. d := (num_divInt_den _).symm

@[deprecated num_divInt_den (since := "2025-08-22")]
abbrev divInt_self := @num_divInt_den

@[simp] theorem zero_divInt (n) : 0 /. n = 0 := by cases n <;> simp [divInt]

@[simp] theorem divInt_zero (n) : n /. 0 = 0 := mkRat_zero n

theorem neg_divInt_neg (num den) : -num /. -den = num /. den := by
  match den with
  | Nat.succ n =>
    simp only [divInt, Int.neg_ofNat_succ]
    simp [normalize_eq_mkRat, Int.neg_neg]
  | 0 => rfl
  | Int.negSucc n =>
    simp only [divInt, Int.neg_negSucc]
    simp [normalize_eq_mkRat]

theorem divInt_neg' (num den) : num /. -den = -num /. den := by rw [← neg_divInt_neg, Int.neg_neg]

theorem divInt_eq_divInt_iff (z₁ : d₁ ≠ 0) (z₂ : d₂ ≠ 0) :
    n₁ /. d₁ = n₂ /. d₂ ↔ n₁ * d₂ = n₂ * d₁ := by
  rcases Int.eq_nat_or_neg d₁ with ⟨_, rfl | rfl⟩ <;>
  rcases Int.eq_nat_or_neg d₂ with ⟨_, rfl | rfl⟩ <;>
  simp_all [divInt_neg', Int.neg_eq_zero,
    mkRat_eq_iff, Int.neg_mul, Int.mul_neg, Int.eq_neg_comm, eq_comm]

@[deprecated divInt_eq_divInt_iff (since := "2025-08-22")]
abbrev divInt_eq_iff := @divInt_eq_divInt_iff

theorem divInt_mul_left {a : Int} (a0 : a ≠ 0) : (a * n) /. (a * d) = n /. d := by
  if d0 : d = 0 then simp [d0] else
  simp [divInt_eq_divInt_iff (Int.mul_ne_zero a0 d0) d0, Int.mul_assoc, Int.mul_left_comm]

theorem divInt_mul_right {a : Int} (a0 : a ≠ 0) : (n * a) /. (d * a) = n /. d := by
  simp [← divInt_mul_left (d := d) a0, Int.mul_comm]

theorem divInt_self' {n : Int} (hn : n ≠ 0) : n /. n = 1 := by
  simpa using divInt_mul_right (n := 1) (d := 1) hn

theorem divInt_num_den (z : d ≠ 0) (h : n /. d = ⟨n', d', z', c⟩) :
    ∃ m, m ≠ 0 ∧ n = n' * m ∧ d = d' * m := by
  rcases Int.eq_nat_or_neg d with ⟨_, rfl | rfl⟩ <;>
    simp_all [divInt_neg', Int.neg_eq_zero]
  · have ⟨m, h₁, h₂⟩ := mkRat_num_den z h; exists m
    simp [Int.natCast_mul, h₁, h₂]
  · have ⟨m, h₁, h₂⟩ := mkRat_num_den z h; exists -m
    rw [← Int.neg_inj, Int.neg_neg] at h₂
    simp [Int.natCast_mul, h₁, h₂, Int.mul_neg, Int.neg_eq_zero]

/-- Define a (dependent) function or prove `∀ r : Rat, p r` by dealing with rational
numbers of the form `n /. d` with `0 < d` and coprime `n`, `d`. -/
@[elab_as_elim]
def numDenCasesOn.{u} {C : Rat → Sort u} :
    ∀ (a : Rat) (_ : ∀ n d, 0 < d → (Int.natAbs n).Coprime d → C (n /. d)), C a
  | ⟨n, d, h, c⟩, H => by rw [mk'_eq_divInt]; exact H n d (Nat.pos_of_ne_zero h) c

/-- Define a (dependent) function or prove `∀ r : Rat, p r` by dealing with rational
numbers of the form `n /. d` with `d ≠ 0`. -/
@[elab_as_elim]
def numDenCasesOn'.{u} {C : Rat → Sort u} (a : Rat) (H : ∀ (n : Int) (d : Nat), d ≠ 0 → C (n /. d)) :
    C a :=
  numDenCasesOn a fun n d h _ => H n d (Nat.ne_of_gt h)

/-- Define a (dependent) function or prove `∀ r : Rat, p r` by dealing with rational
numbers of the form `mk' n d` with `d ≠ 0`. -/
@[elab_as_elim]
def numDenCasesOn''.{u} {C : Rat → Sort u} (a : Rat)
    (H : ∀ (n : Int) (d : Nat) (nz red), C (mk' n d nz red)) : C a :=
  numDenCasesOn a fun n d h h' ↦ by rw [← mk_eq_divInt _ _ (Nat.ne_of_gt h) h']; exact H n d (Nat.ne_of_gt h) _

@[simp] protected theorem ofInt_ofNat : ofInt (OfNat.ofNat n) = OfNat.ofNat n := rfl

@[simp] theorem ofInt_num : (ofInt n : Rat).num = n := rfl
@[simp] theorem ofInt_den : (ofInt n : Rat).den = 1 := rfl

@[simp] theorem num_ofNat : (OfNat.ofNat n : Rat).num = OfNat.ofNat n := rfl
@[simp] theorem den_ofNat : (OfNat.ofNat n : Rat).den = 1 := rfl

@[deprecated num_ofNat (since := "2025-08-22")]
abbrev ofNat_num := @num_ofNat
@[deprecated den_ofNat (since := "2025-08-22")]
abbrev ofNat_den := @den_ofNat

theorem add_def (a b : Rat) :
    a + b = normalize (a.num * b.den + b.num * a.den) (a.den * b.den)
      (Nat.mul_ne_zero a.den_nz b.den_nz) := by
  show Rat.add .. = _; delta Rat.add; dsimp only; split
  · exact (normalize_self _).symm
  · have : a.den.gcd b.den ≠ 0 := Nat.gcd_ne_zero_left a.den_nz
    rw [maybeNormalize_eq_normalize _ _ _ _
        (Int.ofNat_dvd_left.2 <| Nat.gcd_dvd_left ..)
        (Nat.dvd_trans (Nat.gcd_dvd_right ..) <|
         Nat.dvd_trans (Nat.gcd_dvd_right ..) (Nat.dvd_mul_left ..)),
      ← normalize_mul_right _ this]; congr 1
    · simp only [Int.add_mul, Int.mul_assoc, Int.ofNat_mul_ofNat,
        Nat.div_mul_cancel (Nat.gcd_dvd_left ..), Nat.div_mul_cancel (Nat.gcd_dvd_right ..)]
    · rw [Nat.mul_right_comm, Nat.div_mul_cancel (Nat.gcd_dvd_left ..)]

theorem add_def' (a b : Rat) : a + b = mkRat (a.num * b.den + b.num * a.den) (a.den * b.den) := by
  rw [add_def, normalize_eq_mkRat]

@[simp] protected theorem add_zero (a : Rat) : a + 0 = a := by simp [add_def', mkRat_self]
@[simp] protected theorem zero_add (a : Rat) : 0 + a = a := by simp [add_def', mkRat_self]

theorem normalize_add_normalize (n₁ n₂) {d₁ d₂} (z₁ z₂) :
    normalize n₁ d₁ z₁ + normalize n₂ d₂ z₂ =
    normalize (n₁ * d₂ + n₂ * d₁) (d₁ * d₂) (Nat.mul_ne_zero z₁ z₂) := by
  cases e₁ : normalize n₁ d₁ z₁; rcases normalize_num_den e₁ with ⟨g₁, zg₁, rfl, rfl⟩
  cases e₂ : normalize n₂ d₂ z₂; rcases normalize_num_den e₂ with ⟨g₂, zg₂, rfl, rfl⟩
  simp only [add_def]; rw [← normalize_mul_right _ (Nat.mul_ne_zero zg₁ zg₂)]; congr 1
  · rw [Int.add_mul]; simp [Int.natCast_mul, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
  · simp [Nat.mul_left_comm, Nat.mul_comm]

theorem mkRat_add_mkRat (n₁ n₂ : Int) {d₁ d₂} (z₁ : d₁ ≠ 0) (z₂ : d₂ ≠ 0) :
    mkRat n₁ d₁ + mkRat n₂ d₂ = mkRat (n₁ * d₂ + n₂ * d₁) (d₁ * d₂) := by
  rw [← normalize_eq_mkRat z₁, ← normalize_eq_mkRat z₂, normalize_add_normalize, normalize_eq_mkRat]

@[simp]
theorem divInt_add_divInt (n₁ n₂ : Int) {d₁ d₂} (z₁ : d₁ ≠ 0) (z₂ : d₂ ≠ 0) :
    n₁ /. d₁ + n₂ /. d₂ = (n₁ * d₂ + n₂ * d₁) /. (d₁ * d₂) := by
  rcases Int.eq_nat_or_neg d₁ with ⟨_, rfl | rfl⟩ <;>
  rcases Int.eq_nat_or_neg d₂ with ⟨_, rfl | rfl⟩ <;>
  simp_all [← Int.natCast_mul, Int.neg_eq_zero, divInt_neg', Int.mul_neg,
    Int.neg_add, Int.neg_mul, mkRat_add_mkRat]

protected theorem add_comm (a b : Rat) : a + b = b + a := by
  simp [add_def, Int.add_comm, Nat.mul_comm]

protected theorem add_assoc (a b c : Rat) : a + b + c = a + (b + c) :=
  numDenCasesOn' a fun n₁ d₁ h₁ ↦ numDenCasesOn' b fun n₂ d₂ h₂ ↦ numDenCasesOn' c fun n₃ d₃ h₃ ↦ by
    simp only [ne_eq, Int.natCast_eq_zero, h₁, not_false_eq_true, h₂, divInt_add_divInt,
      Int.mul_eq_zero, or_self, h₃]
    rw [Int.mul_assoc, Int.add_mul, Int.add_mul, Int.mul_assoc, Int.add_assoc]
    simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]

protected theorem add_left_comm (a b c : Rat) : a + (b + c) = b + (a + c) := by
  rw [← Rat.add_assoc, Rat.add_comm a, Rat.add_assoc]

@[simp] theorem neg_num (a : Rat) : (-a).num = -a.num := rfl
@[simp] theorem neg_den (a : Rat) : (-a).den = a.den := rfl

theorem neg_normalize (n d z) : -normalize n d z = normalize (-n) d z := by
  simp only [normalize, maybeNormalize_eq, Int.divExact_eq_tdiv, Int.natAbs_neg, Int.neg_tdiv]
  rfl

theorem neg_mkRat (n d) : -mkRat n d = mkRat (-n) d := by
  if z : d = 0 then simp [z]; rfl else simp [← normalize_eq_mkRat z, neg_normalize]

@[simp]
theorem neg_divInt (n d) : -(n /. d) = -n /. d := by
  rcases Int.eq_nat_or_neg d with ⟨_, rfl | rfl⟩ <;> simp [divInt_neg', neg_mkRat]

protected theorem neg_add_cancel (a : Rat) : -a + a = 0 := by
  simp [add_def', Int.neg_mul, Int.add_comm, ← Int.sub_eq_add_neg]

protected theorem add_neg_cancel (a : Rat) : a + -a = 0 := by
  rw [Rat.add_comm, Rat.neg_add_cancel]

protected theorem add_right_cancel {a b : Rat} (c : Rat) (h : a + c = b + c) : a = b := by
  simpa only [Rat.add_assoc, Rat.add_zero, Rat.add_neg_cancel] using congrArg (· + -c) h

theorem sub_def (a b : Rat) :
    a - b = normalize (a.num * b.den - b.num * a.den) (a.den * b.den)
      (Nat.mul_ne_zero a.den_nz b.den_nz) := by
  show Rat.sub .. = _; delta Rat.sub; dsimp only; split
  · exact (normalize_self _).symm
  · have : a.den.gcd b.den ≠ 0 := Nat.gcd_ne_zero_left a.den_nz
    rw [maybeNormalize_eq_normalize _ _ _ _
        (Int.ofNat_dvd_left.2 <| Nat.gcd_dvd_left ..)
        (Nat.dvd_trans (Nat.gcd_dvd_right ..) <|
         Nat.dvd_trans (Nat.gcd_dvd_right ..) (Nat.dvd_mul_left ..)),
      ← normalize_mul_right _ this]; congr 1
    · simp only [Int.sub_mul, Int.mul_assoc, ← Int.natCast_mul,
        Nat.div_mul_cancel (Nat.gcd_dvd_left ..), Nat.div_mul_cancel (Nat.gcd_dvd_right ..)]
    · rw [Nat.mul_right_comm, Nat.div_mul_cancel (Nat.gcd_dvd_left ..)]

theorem sub_def' (a b : Rat) : a - b = mkRat (a.num * b.den - b.num * a.den) (a.den * b.den) := by
  rw [sub_def, normalize_eq_mkRat]

protected theorem sub_eq_add_neg (a b : Rat) : a - b = a + -b := by
  simp [add_def, sub_def, Int.neg_mul, Int.sub_eq_add_neg]

protected theorem neg_sub (a b : Rat) : -(a - b) = b - a := by
  apply Rat.add_right_cancel (a - b)
  rw [Rat.neg_add_cancel, Rat.sub_eq_add_neg, Rat.sub_eq_add_neg, ← Rat.add_assoc, Rat.add_assoc b,
    Rat.neg_add_cancel, Rat.add_zero, Rat.add_neg_cancel]

@[simp]
theorem divInt_sub_divInt (n₁ n₂ : Int) {d₁ d₂} (z₁ : d₁ ≠ 0) (z₂ : d₂ ≠ 0) :
    n₁ /. d₁ - n₂ /. d₂ = (n₁ * d₂ - n₂ * d₁) /. (d₁ * d₂) := by
  simp only [Rat.sub_eq_add_neg, neg_divInt,
    divInt_add_divInt _ _ z₁ z₂, Int.neg_mul, Int.sub_eq_add_neg]

theorem mul_def (a b : Rat) :
    a * b = normalize (a.num * b.num) (a.den * b.den) (Nat.mul_ne_zero a.den_nz b.den_nz) := by
  show Rat.mul .. = _; delta Rat.mul; dsimp only
  have H1 : a.num.natAbs.gcd b.den ≠ 0 := Nat.gcd_ne_zero_right b.den_nz
  have H2 : b.num.natAbs.gcd a.den ≠ 0 := Nat.gcd_ne_zero_right a.den_nz
  simp only [Int.divExact_eq_tdiv, Nat.divExact_eq_div]
  rw [mk_eq_normalize, ← normalize_mul_right _ (Nat.mul_ne_zero H1 H2)]; congr 1
  · rw [Int.natCast_mul, ← Int.mul_assoc, Int.mul_right_comm (Int.tdiv ..),
      Int.tdiv_mul_cancel (Int.ofNat_dvd_left.2 <| Nat.gcd_dvd_left ..), Int.mul_assoc,
      Int.tdiv_mul_cancel (Int.ofNat_dvd_left.2 <| Nat.gcd_dvd_left ..)]
  · rw [← Nat.mul_assoc, Nat.mul_right_comm, Nat.mul_right_comm (_/_),
      Nat.div_mul_cancel (Nat.gcd_dvd_right ..), Nat.mul_assoc,
      Nat.div_mul_cancel (Nat.gcd_dvd_right ..)]

theorem mul_def' (a b : Rat) : a * b = mkRat (a.num * b.num) (a.den * b.den) := by
  rw [mul_def, normalize_eq_mkRat]

protected theorem mul_comm (a b : Rat) : a * b = b * a := by
  simp [mul_def, normalize_eq_mkRat, Int.mul_comm, Nat.mul_comm]

@[simp] protected theorem zero_mul (a : Rat) : 0 * a = 0 := by simp [mul_def]
@[simp] protected theorem mul_zero (a : Rat) : a * 0 = 0 := by simp [mul_def]
@[simp] protected theorem one_mul (a : Rat) : 1 * a = a := by simp [mul_def, normalize_self]
@[simp] protected theorem mul_one (a : Rat) : a * 1 = a := by simp [mul_def, normalize_self]

theorem normalize_mul_normalize (n₁ n₂) {d₁ d₂} (z₁ z₂) :
    normalize n₁ d₁ z₁ * normalize n₂ d₂ z₂ =
    normalize (n₁ * n₂) (d₁ * d₂) (Nat.mul_ne_zero z₁ z₂) := by
  cases e₁ : normalize n₁ d₁ z₁; rcases normalize_num_den e₁ with ⟨g₁, zg₁, rfl, rfl⟩
  cases e₂ : normalize n₂ d₂ z₂; rcases normalize_num_den e₂ with ⟨g₂, zg₂, rfl, rfl⟩
  simp only [mul_def]; rw [← normalize_mul_right _ (Nat.mul_ne_zero zg₁ zg₂)]; congr 1
  · simp [Int.natCast_mul, Int.mul_assoc, Int.mul_left_comm]
  · simp [Nat.mul_left_comm, Nat.mul_comm]

@[simp]
theorem mkRat_mul_mkRat (n₁ n₂ : Int) (d₁ d₂) :
    mkRat n₁ d₁ * mkRat n₂ d₂ = mkRat (n₁ * n₂) (d₁ * d₂) := by
  if z₁ : d₁ = 0 then simp [z₁] else if z₂ : d₂ = 0 then simp [z₂] else
  rw [← normalize_eq_mkRat z₁, ← normalize_eq_mkRat z₂, normalize_mul_normalize, normalize_eq_mkRat]

theorem divInt_mul_divInt (n₁ n₂ : Int) {d₁ d₂} (z₁ : d₁ ≠ 0) (z₂ : d₂ ≠ 0) :
    (n₁ /. d₁) * (n₂ /. d₂) = (n₁ * n₂) /. (d₁ * d₂) := by
  rcases Int.eq_nat_or_neg d₁ with ⟨_, rfl | rfl⟩ <;>
  rcases Int.eq_nat_or_neg d₂ with ⟨_, rfl | rfl⟩ <;>
  simp_all [← Int.natCast_mul, divInt_neg', Int.mul_neg, Int.neg_mul, mkRat_mul_mkRat]

protected theorem mul_assoc (a b c : Rat) : a * b * c = a * (b * c) :=
  numDenCasesOn' a fun n₁ d₁ h₁ =>
    numDenCasesOn' b fun n₂ d₂ h₂ =>
      numDenCasesOn' c fun n₃ d₃ h₃ => by
        simp [Int.mul_comm, Nat.mul_assoc, Int.mul_left_comm]

protected theorem add_mul (a b c : Rat) : (a + b) * c = a * c + b * c :=
  numDenCasesOn' a fun n₁ d₁ h₁ ↦ numDenCasesOn' b fun n₂ d₂ h₂ ↦ numDenCasesOn' c fun n₃ d₃ h₃ ↦ by
    simp only [ne_eq, Int.natCast_eq_zero, h₁, not_false_eq_true, h₂, divInt_add_divInt,
      Int.mul_eq_zero, or_self, h₃, divInt_mul_divInt]
    rw [← divInt_mul_right (mt Int.natCast_eq_zero.mp h₃), Int.add_mul, Int.add_mul]
    simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]

protected theorem mul_add (a b c : Rat) : a * (b + c) = a * b + a * c := by
  rw [Rat.mul_comm, Rat.add_mul, Rat.mul_comm, Rat.mul_comm c a]

protected theorem neg_mul (a b : Rat) : -a * b = -(a * b) := by
  apply Rat.add_right_cancel (a * b)
  simp [← Rat.add_mul, Rat.neg_add_cancel]

protected theorem mul_neg (a b : Rat) : a * -b = -(a * b) := by
  apply Rat.add_right_cancel (a * b)
  simp [← Rat.mul_add, Rat.neg_add_cancel]

theorem inv_def (a : Rat) : a⁻¹ = (a.den : Int) /. a.num := by
  change Rat.inv _ = _
  unfold Rat.inv; split
  · next h => rw [mk_eq_divInt, ← Int.natAbs_neg,
      Int.natAbs_of_nonneg (Int.le_of_lt <| Int.neg_pos_of_neg h), neg_divInt_neg]
  split
  · next h => rw [mk_eq_divInt, Int.natAbs_of_nonneg (Int.le_of_lt h)]
  · next h₁ h₂ =>
    apply (num_divInt_den _).symm.trans
    simp [Int.le_antisymm (Int.not_lt.1 h₂) (Int.not_lt.1 h₁)]

@[simp] protected theorem inv_zero : (0 : Rat)⁻¹ = 0 := by
  change Rat.inv 0 = 0; unfold Rat.inv; rfl

@[simp] theorem inv_divInt (n d : Int) : (n /. d)⁻¹ = d /. n := by
  if z : d = 0 then simp [z] else
  cases e : n /. d; rcases divInt_num_den z e with ⟨g, zg, rfl, rfl⟩
  simp [inv_def, divInt_mul_right zg]

protected theorem mul_inv_cancel (a : Rat) : a ≠ 0 → a * a⁻¹ = 1 :=
  numDenCasesOn' a fun n d hd hn ↦ by
    simp only [divInt_ofNat, ne_eq, hd, not_false_eq_true, mkRat_eq_zero] at hn
    simp only [inv_divInt, ne_eq, Int.natCast_eq_zero, hd, not_false_eq_true, hn, divInt_mul_divInt,
      Int.mul_comm, Int.mul_eq_zero, or_self, divInt_self']

protected theorem inv_mul_cancel (a : Rat) (h : a ≠ 0) : a⁻¹ * a = 1 :=
  Eq.trans (Rat.mul_comm _ _) (Rat.mul_inv_cancel _ h)

protected theorem inv_inv (a : Rat) : a⁻¹⁻¹ = a :=
  numDenCasesOn' a fun n d hd ↦ by simp only [inv_divInt]

protected theorem mul_eq_zero {a b : Rat} : a * b = 0 ↔ a = 0 ∨ b = 0 := by
  constructor
  · intro h
    replace h := congrArg (· * b⁻¹) h
    apply Decidable.byContradiction fun h' => ?_
    rw [not_or] at h'
    simp only [Rat.zero_mul, Rat.mul_assoc, Rat.mul_inv_cancel _ h'.2, Rat.mul_one] at h
    exact absurd h h'.1
  · rintro (h | h) <;> simp [h]

theorem div_def (a b : Rat) : a / b = a * b⁻¹ := rfl

theorem pow_def (q : Rat) (n : Nat) :
    q ^ n = ⟨q.num ^ n, q.den ^ n, by simp [q.den_nz],
      by rw [Int.natAbs_pow]; exact q.reduced.pow _ _⟩ := rfl

protected theorem pow_zero (q : Rat) : q ^ 0 = 1 := rfl

protected theorem pow_succ (q : Rat) (n : Nat) : q ^ (n + 1) = q ^ n * q := by
  rcases q with ⟨n, d, hn, r⟩
  simp only [pow_def, Int.pow_succ, Nat.pow_succ]
  simp only [mk'_eq_divInt, divInt_mul_divInt, Int.natCast_eq_zero, hn, Nat.pow_eq_zero,
    not_false_eq_true, false_and, ne_eq, Int.natCast_mul]

protected theorem zpow_zero (q : Rat) : q ^ (0 : Int) = 1 := Rat.pow_zero q

protected theorem zpow_natCast (q : Rat) (n : Nat) : q ^ (n : Int) = q ^ n := rfl

protected theorem zpow_neg (q : Rat) (n : Int) : q ^ (-n : Int) = (q ^ n)⁻¹ := by
  rcases n with (_ | n) | n
  · with_unfolding_all rfl
  · rfl
  · exact (Rat.inv_inv _).symm

/-! ### `ofScientific` -/

theorem ofScientific_true_def : Rat.ofScientific m true e = mkRat m (10 ^ e) := by
  unfold Rat.ofScientific; rw [normalize_eq_mkRat]; rfl

theorem ofScientific_false_def : Rat.ofScientific m false e = (m * 10 ^ e : Nat) := by
  unfold Rat.ofScientific; rfl

theorem ofScientific_def : Rat.ofScientific m s e =
    if s then mkRat m (10 ^ e) else (m * 10 ^ e : Nat) := by
  cases s; exact ofScientific_false_def; exact ofScientific_true_def

/-- `Rat.ofScientific` applied to numeric literals is the same as a scientific literal. -/
@[simp]
theorem ofScientific_ofNat_ofNat :
    Rat.ofScientific (no_index (OfNat.ofNat m)) s (no_index (OfNat.ofNat e))
      = OfScientific.ofScientific m s e := rfl

/-! ### `intCast` -/

@[simp] theorem den_intCast (a : Int) : (a : Rat).den = 1 := rfl

@[simp] theorem num_intCast (a : Int) : (a : Rat).num = a := rfl

@[deprecated den_intCast (since := "2025-08-22")]
abbrev intCast_den := @den_intCast
@[deprecated num_intCast (since := "2025-08-22")]
abbrev intCast_num := @num_intCast

@[simp, norm_cast] theorem intCast_inj {a b : Int} : (a : Rat) = (b : Rat) ↔ a = b := by
  constructor
  · rintro ⟨⟩; rfl
  · simp_all

protected theorem intCast_zero : ((0 : Int) : Rat) = (0 : Rat) := rfl

protected theorem intCast_one : ((1 : Int) : Rat) = (1 : Rat) := rfl

@[simp, norm_cast] protected theorem intCast_add (a b : Int) :
    ((a + b : Int) : Rat) = (a : Rat) + (b : Rat) := by
  rw [add_def]
  simp [normalize_eq]

@[simp, norm_cast] protected theorem intCast_neg (a : Int) : ((-a : Int) : Rat) = -(a : Rat) := rfl

@[simp, norm_cast] protected theorem intCast_sub (a b : Int) :
    ((a - b : Int) : Rat) = (a : Rat) - (b : Rat) := by
  rw [sub_def]
  simp [normalize_eq]

@[simp, norm_cast] protected theorem intCast_mul (a b : Int) :
    ((a * b : Int) : Rat) = (a : Rat) * (b : Rat) := by
  rw [mul_def]
  simp [normalize_eq]

/-! ### `≤` and `<` -/

@[simp] theorem num_nonneg {q : Rat} : 0 ≤ q.num ↔ 0 ≤ q := by
  simp [instLE, Rat.blt, imp.swap]

@[simp]
theorem num_eq_zero {q : Rat} : q.num = 0 ↔ q = 0 := by
  induction q
  constructor
  · rintro rfl
    rw [mk'_eq_divInt, zero_divInt]
  · exact congrArg Rat.num

protected theorem nonneg_antisymm {q : Rat} : 0 ≤ q → 0 ≤ -q → q = 0 := by
  simp only [← num_nonneg, neg_num, ← num_eq_zero]
  omega

protected theorem nonneg_total (a : Rat) : 0 ≤ a ∨ 0 ≤ -a := by
  simpa only [← num_nonneg, neg_num, ← num_eq_zero, Int.neg_nonneg] using Int.le_total _ _

@[simp] theorem divInt_nonneg_iff_of_pos_right {a b : Int} (hb : 0 < b) :
    0 ≤ a /. b ↔ 0 ≤ a := by
  rcases hab : a /. b with ⟨n, d, hd, hnd⟩
  rw [mk'_eq_divInt, divInt_eq_divInt_iff (Int.ne_of_gt hb) (mod_cast hd)] at hab
  rw [← num_nonneg, ← Int.mul_nonneg_iff_of_pos_right hb, ← hab,
    Int.mul_nonneg_iff_of_pos_right (mod_cast Nat.pos_of_ne_zero hd)]

@[simp] theorem divInt_nonneg {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a /. b := by
  obtain hb | rfl := Int.le_iff_lt_or_eq.mp hb
  · rwa [divInt_nonneg_iff_of_pos_right hb]
  · rfl

protected theorem add_nonneg {a b : Rat} : 0 ≤ a → 0 ≤ b → 0 ≤ a + b :=
  numDenCasesOn' a fun n₁ d₁ h₁ ↦ numDenCasesOn' b fun n₂ d₂ h₂ ↦ by
    have d₁0 : 0 < (d₁ : Int) := mod_cast Nat.pos_of_ne_zero h₁
    have d₂0 : 0 < (d₂ : Int) := mod_cast Nat.pos_of_ne_zero h₂
    simp only [d₁0, d₂0, h₁, h₂, Int.mul_pos, divInt_nonneg_iff_of_pos_right, divInt_add_divInt,
      ne_eq, Int.natCast_eq_zero, not_false_eq_true]
    intro n₁0 n₂0
    apply Int.add_nonneg <;> apply Int.mul_nonneg <;> · first | assumption | apply Int.ofNat_zero_le

protected theorem mul_nonneg {a b : Rat} : 0 ≤ a → 0 ≤ b → 0 ≤ a * b :=
  numDenCasesOn' a fun n₁ d₁ h₁ =>
    numDenCasesOn' b fun n₂ d₂ h₂ => by
      have d₁0 : 0 < (d₁ : Int) := mod_cast Nat.pos_of_ne_zero h₁
      have d₂0 : 0 < (d₂ : Int) := mod_cast Nat.pos_of_ne_zero h₂
      simp only [d₁0, d₂0, Int.mul_pos, divInt_nonneg_iff_of_pos_right,
        divInt_mul_divInt _ _ (Int.ne_of_gt d₁0) (Int.ne_of_gt d₂0)]
      apply Int.mul_nonneg

protected theorem not_le {a b : Rat} : ¬a ≤ b ↔ b < a := (Bool.not_eq_false _).to_iff
protected theorem not_lt {a b : Rat} : ¬a < b ↔ b ≤ a := (Bool.not_eq_true _).to_iff

protected theorem lt_iff (a b : Rat) : a < b ↔ a.num * b.den < b.num * a.den :=
  numDenCasesOn'' a fun na da ha hared =>
    numDenCasesOn'' b fun nb db hb hbred => by
      change Rat.blt _ _ = true ↔ _
      suffices
        (na < 0 ∧ 0 ≤ nb ∨ if na = 0 then 0 < nb else (na ≤ 0 ∨ 0 < nb) ∧ na * ↑db < nb * da) ↔
        na * db < nb * da by simpa [Rat.blt]
      split
      · simp_all
      · constructor
        · refine (·.elim ?_ And.right)
          rintro ⟨hna, nb0⟩
          refine Int.lt_of_lt_of_le (Int.mul_neg_of_neg_of_pos hna ?_) (Int.mul_nonneg nb0 ?_)
          · simpa using Nat.pos_of_ne_zero hb
          · simp
        · intro h
          simp only [h, and_true]
          false_or_by_contra
          apply Int.not_le.mpr h
          apply Int.le_trans (Int.mul_nonpos_of_nonpos_of_nonneg _ _) (Int.mul_nonneg _ _) <;> omega

protected theorem le_iff (a b : Rat) : a ≤ b ↔ a.num * b.den ≤ b.num * a.den := by
  simpa only [Rat.not_lt, Int.not_lt] using not_congr (Rat.lt_iff b a)

protected theorem le_iff_sub_nonneg (a b : Rat) : a ≤ b ↔ 0 ≤ b - a :=
  numDenCasesOn'' a fun na da ha hared =>
    numDenCasesOn'' b fun nb db hb hbred => by
      rw [Rat.le_iff, sub_def, normalize_eq, ← num_nonneg, ← Int.sub_nonneg]
      dsimp only
      refine ⟨(Int.ediv_nonneg · (Int.natCast_nonneg _)), fun H ↦ ?_⟩
      apply (Int.ediv_nonneg_iff_of_pos _).mp H
      simp only [Int.natCast_pos, Nat.pos_iff_ne_zero]
      exact Nat.gcd_ne_zero_right (Nat.mul_ne_zero hb ha)

protected theorem le_total {a b : Rat} : a ≤ b ∨ b ≤ a := by
  simpa only [← Rat.le_iff_sub_nonneg, Rat.neg_sub] using Rat.nonneg_total (b - a)

protected theorem le_refl {a : Rat} : a ≤ a := by
  rw [Rat.le_iff_sub_nonneg, ← num_nonneg, sub_def]
  simp

protected theorem le_trans {a b c : Rat} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  rw [Rat.le_iff_sub_nonneg] at hab hbc
  have := Rat.add_nonneg hab hbc
  replace : 0 ≤ c + -a + (-b + b) := by
    simpa [Rat.sub_eq_add_neg, Rat.add_comm, Rat.add_assoc, Rat.add_left_comm] using this
  rwa [Rat.neg_add_cancel, Rat.add_zero, ← Rat.sub_eq_add_neg, ← Rat.le_iff_sub_nonneg] at this

protected theorem le_antisymm {a b : Rat} (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  rw [Rat.le_iff_sub_nonneg] at hab hba
  rw [Rat.sub_eq_add_neg] at hba
  rw [← Rat.neg_sub, Rat.sub_eq_add_neg] at hab
  have := congrArg (· + b) (Rat.nonneg_antisymm hba hab)
  simpa only [Rat.add_assoc, Rat.neg_add_cancel, Rat.zero_add, Rat.add_zero] using this

protected theorem le_of_lt {a b : Rat} (ha : a < b) : a ≤ b :=
  Rat.le_total.resolve_left (Rat.not_le.mpr ha)

protected theorem ne_of_lt {a b : Rat} (ha : a < b) : a ≠ b := by
  intro rfl
  exact Rat.not_le.mpr ha Rat.le_refl

protected theorem ne_of_gt {a b : Rat} (ha : a < b) : b ≠ a :=
  (Rat.ne_of_lt ha).symm

protected theorem lt_of_le_of_ne {a b : Rat} (ha : a ≤ b) (hb : a ≠ b) : a < b :=
  Rat.not_le.mp fun h => hb (Rat.le_antisymm ha h)

protected theorem add_le_add_left {a b c : Rat} : c + a ≤ c + b ↔ a ≤ b := by
  rw [Rat.le_iff_sub_nonneg, Rat.le_iff_sub_nonneg a, ← propext_iff]
  congr 1
  apply Rat.add_right_cancel (c + a)
  rw [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.neg_add_cancel, Rat.sub_eq_add_neg,
    Rat.add_zero, Rat.add_assoc, Rat.add_left_comm (-a), Rat.neg_add_cancel, Rat.add_zero,
    Rat.add_comm]

protected theorem lt_iff_sub_pos (a b : Rat) : a < b ↔ 0 < b - a := by
  simp only [← Rat.not_le]
  apply not_congr
  constructor
  · intro h
    simpa [Rat.sub_eq_add_neg, Rat.add_comm, Rat.add_neg_cancel]
      using (Rat.add_le_add_left (c := -a)).mpr h
  · intro h
    simpa [Rat.sub_eq_add_neg, Rat.add_left_comm a, Rat.add_neg_cancel]
      using (Rat.add_le_add_left (c := a)).mpr h

protected theorem mul_pos {a b : Rat} (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  refine Rat.lt_of_le_of_ne (Rat.mul_nonneg (Rat.le_of_lt ha) (Rat.le_of_lt hb)) ?_
  simp [eq_comm, Rat.mul_eq_zero, Rat.ne_of_gt ha, Rat.ne_of_gt hb]

protected theorem mul_lt_mul_of_pos_left {a b c : Rat} (ha : a < b) (hc : 0 < c) :
    c * a < c * b := by
  rw [Rat.lt_iff_sub_pos, Rat.sub_eq_add_neg] at ha ⊢
  rw [← Rat.mul_neg, ← Rat.mul_add]
  exact Rat.mul_pos hc ha

protected theorem mul_lt_mul_of_pos_right {a b c : Rat} (ha : a < b) (hc : 0 < c) :
    a * c < b * c := by
  rw [Rat.lt_iff_sub_pos, Rat.sub_eq_add_neg] at ha ⊢
  rw [← Rat.neg_mul, ← Rat.add_mul]
  exact Rat.mul_pos ha hc
