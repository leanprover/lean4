/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module
prelude

public import Init.Data.Rat.Basic

@[expose] public section

/-! # Additional lemmas about the Rational Numbers -/

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

protected theorem add_zero (a : Rat) : a + 0 = a := by simp [add_def', mkRat_self]
protected theorem zero_add (a : Rat) : 0 + a = a := by simp [add_def', mkRat_self]

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

theorem inv_def (a : Rat) : a.inv = (a.den : Int) /. a.num := by
  unfold Rat.inv; split
  · next h => rw [mk_eq_divInt, ← Int.natAbs_neg,
      Int.natAbs_of_nonneg (Int.le_of_lt <| Int.neg_pos_of_neg h), neg_divInt_neg]
  split
  · next h => rw [mk_eq_divInt, Int.natAbs_of_nonneg (Int.le_of_lt h)]
  · next h₁ h₂ =>
    apply (num_divInt_den _).symm.trans
    simp [Int.le_antisymm (Int.not_lt.1 h₂) (Int.not_lt.1 h₁)]

@[simp] protected theorem inv_zero : (0 : Rat).inv = 0 := by unfold Rat.inv; rfl

@[simp] theorem inv_divInt (n d : Int) : (n /. d).inv = d /. n := by
  if z : d = 0 then simp [z] else
  cases e : n /. d; rcases divInt_num_den z e with ⟨g, zg, rfl, rfl⟩
  simp [inv_def, divInt_mul_right zg]

theorem div_def (a b : Rat) : a / b = a * b.inv := rfl

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
