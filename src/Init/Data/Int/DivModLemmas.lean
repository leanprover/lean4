/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro
-/

prelude
import Init.Data.Int.DivMod
import Init.Data.Int.Order
import Init.Data.Nat.Dvd

/-!
# Lemmas about integer division needed to bootstrap `omega`.
-/


open Nat (succ)

namespace Int

/-! ### `/`  -/

@[simp] theorem zero_ediv : ∀ b : Int, 0 / b = 0
  | ofNat _ => show ofNat _ = _ by simp
  | -[_+1] => show -ofNat _ = _ by simp

@[simp] protected theorem ediv_zero : ∀ a : Int, a / 0 = 0
  | ofNat _ => show ofNat _ = _ by simp
  | -[_+1] => rfl


@[simp] protected theorem ediv_neg : ∀ a b : Int, a / (-b) = -(a / b)
  | ofNat m, 0 => show ofNat (m / 0) = -↑(m / 0) by rw [Nat.div_zero]; rfl
  | ofNat m, -[n+1] => (Int.neg_neg _).symm
  | ofNat m, succ n | -[m+1], 0 | -[m+1], succ n | -[m+1], -[n+1] => rfl

protected theorem div_def (a b : Int) : a / b = Int.ediv a b := rfl

theorem add_mul_ediv_right (a b : Int) {c : Int} (H : c ≠ 0) : (a + b * c) / c = a / c + b :=
  suffices ∀ {{a b c : Int}}, 0 < c → (a + b * c).ediv c = a.ediv c + b from
    match Int.lt_trichotomy c 0 with
    | Or.inl hlt => by
      rw [← Int.neg_inj, ← Int.ediv_neg, Int.neg_add, ← Int.ediv_neg, ← Int.neg_mul_neg]
      exact this (Int.neg_pos_of_neg hlt)
    | Or.inr (Or.inl HEq) => absurd HEq H
    | Or.inr (Or.inr hgt) => this hgt
  suffices ∀ {k n : Nat} {a : Int}, (a + n * k.succ).ediv k.succ = a.ediv k.succ + n from
    fun a b c H => match c, eq_succ_of_zero_lt H, b with
      | _, ⟨_, rfl⟩, ofNat _ => this
      | _, ⟨k, rfl⟩, -[n+1] => show (a - n.succ * k.succ).ediv k.succ = a.ediv k.succ - n.succ by
        rw [← Int.add_sub_cancel (ediv ..), ← this, Int.sub_add_cancel]
  fun {k n} => @fun
  | ofNat m => congrArg ofNat <| Nat.add_mul_div_right _ _ k.succ_pos
  | -[m+1] => by
    show ((n * k.succ : Nat) - m.succ : Int).ediv k.succ = n - (m / k.succ + 1 : Nat)
    by_cases h : m < n * k.succ
    · rw [← Int.ofNat_sub h, ← Int.ofNat_sub ((Nat.div_lt_iff_lt_mul k.succ_pos).2 h)]
      apply congrArg ofNat
      rw [Nat.mul_comm, Nat.mul_sub_div]; rwa [Nat.mul_comm]
    · have h := Nat.not_lt.1 h
      have H {a b : Nat} (h : a ≤ b) : (a : Int) + -((b : Int) + 1) = -[b - a +1] := by
        rw [negSucc_eq, Int.ofNat_sub h]
        simp only [Int.sub_eq_add_neg, Int.neg_add, Int.neg_neg, Int.add_left_comm, Int.add_assoc]
      show ediv (↑(n * succ k) + -((m : Int) + 1)) (succ k) = n + -(↑(m / succ k) + 1 : Int)
      rw [H h, H ((Nat.le_div_iff_mul_le k.succ_pos).2 h)]
      apply congrArg negSucc
      rw [Nat.mul_comm, Nat.sub_mul_div]; rwa [Nat.mul_comm]

theorem add_ediv_of_dvd_right {a b c : Int} (H : c ∣ b) : (a + b) / c = a / c + b / c :=
  if h : c = 0 then by simp [h] else by
    let ⟨k, hk⟩ := H
    rw [hk, Int.mul_comm c k, Int.add_mul_ediv_right _ _ h,
      ← Int.zero_add (k * c), Int.add_mul_ediv_right _ _ h, Int.zero_ediv, Int.zero_add]

theorem add_ediv_of_dvd_left {a b c : Int} (H : c ∣ a) : (a + b) / c = a / c + b / c := by
  rw [Int.add_comm, Int.add_ediv_of_dvd_right H, Int.add_comm]

@[simp] theorem mul_ediv_cancel (a : Int) {b : Int} (H : b ≠ 0) : (a * b) / b = a := by
  have := Int.add_mul_ediv_right 0 a H
  rwa [Int.zero_add, Int.zero_ediv, Int.zero_add] at this

@[simp] theorem mul_ediv_cancel_left (b : Int) (H : a ≠ 0) : (a * b) / a = b :=
  Int.mul_comm .. ▸ Int.mul_ediv_cancel _ H

theorem div_nonneg_iff_of_pos {a b : Int} (h : 0 < b) : a / b ≥ 0 ↔ a ≥ 0 := by
  rw [Int.div_def]
  match b, h with
  | Int.ofNat (b+1), _ =>
    rcases a with ⟨a⟩ <;> simp [Int.ediv]
    exact decide_eq_decide.mp rfl

/-! ### mod -/

theorem mod_def' (m n : Int) : m % n = emod m n := rfl

theorem ofNat_mod (m n : Nat) : (↑(m % n) : Int) = mod m n := rfl

theorem ofNat_mod_ofNat (m n : Nat) : (m % n : Int) = ↑(m % n) := rfl

@[simp, norm_cast] theorem ofNat_emod (m n : Nat) : (↑(m % n) : Int) = m % n := rfl

@[simp] theorem zero_emod (b : Int) : 0 % b = 0 := by simp [mod_def', emod]

@[simp] theorem emod_zero : ∀ a : Int, a % 0 = a
  | ofNat _ => congrArg ofNat <| Nat.mod_zero _
  | -[_+1]  => congrArg negSucc <| Nat.mod_zero _

theorem emod_add_ediv : ∀ a b : Int, a % b + b * (a / b) = a
  | ofNat _, ofNat _ => congrArg ofNat <| Nat.mod_add_div ..
  | ofNat m, -[n+1] => by
    show (m % succ n + -↑(succ n) * -↑(m / succ n) : Int) = m
    rw [Int.neg_mul_neg]; exact congrArg ofNat <| Nat.mod_add_div ..
  | -[_+1], 0 => by rw [emod_zero]; rfl
  | -[m+1], succ n => aux m n.succ
  | -[m+1], -[n+1] => aux m n.succ
where
  aux (m n : Nat) : n - (m % n + 1) - (n * (m / n) + n) = -[m+1] := by
    rw [← ofNat_emod, ← ofNat_ediv, ← Int.sub_sub, negSucc_eq, Int.sub_sub n,
      ← Int.neg_neg (_-_), Int.neg_sub, Int.sub_sub_self, Int.add_right_comm]
    exact congrArg (fun x => -(ofNat x + 1)) (Nat.mod_add_div ..)

theorem ediv_add_emod (a b : Int) : b * (a / b) + a % b = a :=
  (Int.add_comm ..).trans (emod_add_ediv ..)

theorem emod_def (a b : Int) : a % b = a - b * (a / b) := by
  rw [← Int.add_sub_cancel (a % b), emod_add_ediv]

theorem emod_nonneg : ∀ (a : Int) {b : Int}, b ≠ 0 → 0 ≤ a % b
  | ofNat _, _, _ => ofNat_zero_le _
  | -[_+1], _, H => Int.sub_nonneg_of_le <| ofNat_le.2 <| Nat.mod_lt _ (natAbs_pos.2 H)

theorem emod_lt_of_pos (a : Int) {b : Int} (H : 0 < b) : a % b < b :=
  match a, b, eq_succ_of_zero_lt H with
  | ofNat _, _, ⟨_, rfl⟩ => ofNat_lt.2 (Nat.mod_lt _ (Nat.succ_pos _))
  | -[_+1], _, ⟨_, rfl⟩ => Int.sub_lt_self _ (ofNat_lt.2 <| Nat.succ_pos _)

theorem mul_ediv_self_le {x k : Int} (h : k ≠ 0) : k * (x / k) ≤ x :=
  calc k * (x / k)
    _ ≤ k * (x / k) + x % k := Int.le_add_of_nonneg_right (emod_nonneg x h)
    _ = x                   := ediv_add_emod _ _

theorem lt_mul_ediv_self_add {x k : Int} (h : 0 < k) : x < k * (x / k) + k :=
  calc x
    _ = k * (x / k) + x % k := (ediv_add_emod _ _).symm
    _ < k * (x / k) + k     := Int.add_lt_add_left (emod_lt_of_pos x h) _

theorem emod_add_ediv' (m k : Int) : m % k + m / k * k = m := by
  rw [Int.mul_comm]; apply emod_add_ediv

@[simp] theorem add_mul_emod_self {a b c : Int} : (a + b * c) % c = a % c :=
  if cz : c = 0 then by
    rw [cz, Int.mul_zero, Int.add_zero]
  else by
    rw [Int.emod_def, Int.emod_def, Int.add_mul_ediv_right _ _ cz, Int.add_comm _ b,
      Int.mul_add, Int.mul_comm, ← Int.sub_sub, Int.add_sub_cancel]

@[simp] theorem add_mul_emod_self_left (a b c : Int) : (a + b * c) % b = a % b := by
  rw [Int.mul_comm, Int.add_mul_emod_self]

@[simp] theorem add_emod_self {a b : Int} : (a + b) % b = a % b := by
  have := add_mul_emod_self_left a b 1; rwa [Int.mul_one] at this

@[simp] theorem add_emod_self_left {a b : Int} : (a + b) % a = b % a := by
  rw [Int.add_comm, Int.add_emod_self]

theorem neg_emod {a b : Int} : -a % b = (b - a) % b := by
  rw [← add_emod_self_left]; rfl

@[simp] theorem emod_add_emod (m n k : Int) : (m % n + k) % n = (m + k) % n := by
  have := (add_mul_emod_self_left (m % n + k) n (m / n)).symm
  rwa [Int.add_right_comm, emod_add_ediv] at this

@[simp] theorem add_emod_emod (m n k : Int) : (m + n % k) % k = (m + n) % k := by
  rw [Int.add_comm, emod_add_emod, Int.add_comm]

theorem add_emod (a b n : Int) : (a + b) % n = (a % n + b % n) % n := by
  rw [add_emod_emod, emod_add_emod]

theorem add_emod_eq_add_emod_right {m n k : Int} (i : Int)
    (H : m % n = k % n) : (m + i) % n = (k + i) % n := by
  rw [← emod_add_emod, ← emod_add_emod k, H]

theorem emod_add_cancel_right {m n k : Int} (i) : (m + i) % n = (k + i) % n ↔ m % n = k % n :=
  ⟨fun H => by
    have := add_emod_eq_add_emod_right (-i) H
    rwa [Int.add_neg_cancel_right, Int.add_neg_cancel_right] at this,
  add_emod_eq_add_emod_right _⟩

@[simp] theorem mul_emod_left (a b : Int) : (a * b) % b = 0 := by
  rw [← Int.zero_add (a * b), Int.add_mul_emod_self, Int.zero_emod]

@[simp] theorem mul_emod_right (a b : Int) : (a * b) % a = 0 := by
  rw [Int.mul_comm, mul_emod_left]

theorem mul_emod (a b n : Int) : (a * b) % n = (a % n) * (b % n) % n := by
  conv => lhs; rw [
    ← emod_add_ediv a n, ← emod_add_ediv' b n, Int.add_mul, Int.mul_add, Int.mul_add,
    Int.mul_assoc, Int.mul_assoc, ← Int.mul_add n _ _, add_mul_emod_self_left,
    ← Int.mul_assoc, add_mul_emod_self]

@[local simp] theorem emod_self {a : Int} : a % a = 0 := by
  have := mul_emod_left 1 a; rwa [Int.one_mul] at this

@[simp] theorem emod_emod_of_dvd (n : Int) {m k : Int}
    (h : m ∣ k) : (n % k) % m = n % m := by
  conv => rhs; rw [← emod_add_ediv n k]
  match k, h with
  | _, ⟨t, rfl⟩ => rw [Int.mul_assoc, add_mul_emod_self_left]

@[simp] theorem emod_emod (a b : Int) : (a % b) % b = a % b := by
  conv => rhs; rw [← emod_add_ediv a b, add_mul_emod_self_left]

theorem sub_emod (a b n : Int) : (a - b) % n = (a % n - b % n) % n := by
  apply (emod_add_cancel_right b).mp
  rw [Int.sub_add_cancel, ← Int.add_emod_emod, Int.sub_add_cancel, emod_emod]

/-! ### properties of `/` and `%` -/

theorem mul_ediv_cancel_of_emod_eq_zero {a b : Int} (H : a % b = 0) : b * (a / b) = a := by
  have := emod_add_ediv a b; rwa [H, Int.zero_add] at this

theorem ediv_mul_cancel_of_emod_eq_zero {a b : Int} (H : a % b = 0) : a / b * b = a := by
  rw [Int.mul_comm, mul_ediv_cancel_of_emod_eq_zero H]

/-! ### dvd -/

protected theorem dvd_zero (n : Int) : n ∣ 0 := ⟨0, (Int.mul_zero _).symm⟩

protected theorem dvd_refl (n : Int) : n ∣ n := ⟨1, (Int.mul_one _).symm⟩

protected theorem one_dvd (n : Int) : 1 ∣ n := ⟨n, (Int.one_mul n).symm⟩

protected theorem dvd_trans : ∀ {a b c : Int}, a ∣ b → b ∣ c → a ∣ c
  | _, _, _, ⟨d, rfl⟩, ⟨e, rfl⟩ => ⟨d * e, by rw [Int.mul_assoc]⟩

@[simp] protected theorem zero_dvd {n : Int} : 0 ∣ n ↔ n = 0 :=
  ⟨fun ⟨k, e⟩ => by rw [e, Int.zero_mul], fun h => h.symm ▸ Int.dvd_refl _⟩

protected theorem neg_dvd {a b : Int} : -a ∣ b ↔ a ∣ b := by
  constructor <;> exact fun ⟨k, e⟩ =>
    ⟨-k, by simp [e, Int.neg_mul, Int.mul_neg, Int.neg_neg]⟩

protected theorem dvd_neg {a b : Int} : a ∣ -b ↔ a ∣ b := by
  constructor <;> exact fun ⟨k, e⟩ =>
    ⟨-k, by simp [← e, Int.neg_mul, Int.mul_neg, Int.neg_neg]⟩

protected theorem dvd_mul_right (a b : Int) : a ∣ a * b := ⟨_, rfl⟩

protected theorem dvd_mul_left (a b : Int) : b ∣ a * b := ⟨_, Int.mul_comm ..⟩

protected theorem dvd_add : ∀ {a b c : Int}, a ∣ b → a ∣ c → a ∣ b + c
  | _, _, _, ⟨d, rfl⟩, ⟨e, rfl⟩ => ⟨d + e, by rw [Int.mul_add]⟩

protected theorem dvd_sub : ∀ {a b c : Int}, a ∣ b → a ∣ c → a ∣ b - c
  | _, _, _, ⟨d, rfl⟩, ⟨e, rfl⟩ => ⟨d - e, by rw [Int.mul_sub]⟩


@[norm_cast] theorem ofNat_dvd {m n : Nat} : (↑m : Int) ∣ ↑n ↔ m ∣ n := by
  refine ⟨fun ⟨a, ae⟩ => ?_, fun ⟨k, e⟩ => ⟨k, by rw [e, Int.ofNat_mul]⟩⟩
  match Int.le_total a 0 with
  | .inl h =>
    have := ae.symm ▸ Int.mul_nonpos_of_nonneg_of_nonpos (ofNat_zero_le _) h
    rw [Nat.le_antisymm (ofNat_le.1 this) (Nat.zero_le _)]
    apply Nat.dvd_zero
  | .inr h => match a, eq_ofNat_of_zero_le h with
    | _, ⟨k, rfl⟩ => exact ⟨k, Int.ofNat.inj ae⟩

@[simp] theorem natAbs_dvd_natAbs {a b : Int} : natAbs a ∣ natAbs b ↔ a ∣ b := by
  refine ⟨fun ⟨k, hk⟩ => ?_, fun ⟨k, hk⟩ => ⟨natAbs k, hk.symm ▸ natAbs_mul a k⟩⟩
  rw [← natAbs_ofNat k, ← natAbs_mul, natAbs_eq_natAbs_iff] at hk
  cases hk <;> subst b
  · apply Int.dvd_mul_right
  · rw [← Int.mul_neg]; apply Int.dvd_mul_right

theorem ofNat_dvd_left {n : Nat} {z : Int} : (↑n : Int) ∣ z ↔ n ∣ z.natAbs := by
  rw [← natAbs_dvd_natAbs, natAbs_ofNat]

theorem dvd_of_emod_eq_zero {a b : Int} (H : b % a = 0) : a ∣ b :=
  ⟨b / a, (mul_ediv_cancel_of_emod_eq_zero H).symm⟩

theorem dvd_emod_sub_self {x : Int} {m : Nat} : (m : Int) ∣ x % m - x := by
  apply dvd_of_emod_eq_zero
  simp [sub_emod]

theorem emod_eq_zero_of_dvd : ∀ {a b : Int}, a ∣ b → b % a = 0
  | _, _, ⟨_, rfl⟩ => mul_emod_right ..

theorem dvd_iff_emod_eq_zero (a b : Int) : a ∣ b ↔ b % a = 0 :=
  ⟨emod_eq_zero_of_dvd, dvd_of_emod_eq_zero⟩

theorem emod_pos_of_not_dvd {a b : Int} (h : ¬ a ∣ b) : a = 0 ∨ 0 < b % a := by
  rw [dvd_iff_emod_eq_zero] at h
  by_cases w : a = 0
  · simp_all
  · exact Or.inr (Int.lt_iff_le_and_ne.mpr ⟨emod_nonneg b w, Ne.symm h⟩)

instance decidableDvd : DecidableRel (α := Int) (· ∣ ·) := fun _ _ =>
  decidable_of_decidable_of_iff (dvd_iff_emod_eq_zero ..).symm

protected theorem ediv_mul_cancel {a b : Int} (H : b ∣ a) : a / b * b = a :=
  ediv_mul_cancel_of_emod_eq_zero (emod_eq_zero_of_dvd H)

protected theorem mul_ediv_cancel' {a b : Int} (H : a ∣ b) : a * (b / a) = b := by
  rw [Int.mul_comm, Int.ediv_mul_cancel H]

protected theorem mul_ediv_assoc (a : Int) : ∀ {b c : Int}, c ∣ b → (a * b) / c = a * (b / c)
  | _, c, ⟨d, rfl⟩ =>
    if cz : c = 0 then by simp [cz, Int.mul_zero] else by
      rw [Int.mul_left_comm, Int.mul_ediv_cancel_left _ cz, Int.mul_ediv_cancel_left _ cz]

protected theorem mul_ediv_assoc' (b : Int) {a c : Int}
    (h : c ∣ a) : (a * b) / c = a / c * b := by
  rw [Int.mul_comm, Int.mul_ediv_assoc _ h, Int.mul_comm]

theorem neg_ediv_of_dvd : ∀ {a b : Int}, b ∣ a → (-a) / b = -(a / b)
  | _, b, ⟨c, rfl⟩ => by
    by_cases bz : b = 0
    · simp [bz]
    · rw [Int.neg_mul_eq_mul_neg, Int.mul_ediv_cancel_left _ bz, Int.mul_ediv_cancel_left _ bz]

theorem sub_ediv_of_dvd (a : Int) {b c : Int}
    (hcb : c ∣ b) : (a - b) / c = a / c - b / c := by
  rw [Int.sub_eq_add_neg, Int.sub_eq_add_neg, Int.add_ediv_of_dvd_right (Int.dvd_neg.2 hcb)]
  congr; exact Int.neg_ediv_of_dvd hcb

@[simp] theorem ediv_one : ∀ a : Int, a / 1 = a
  | (_:Nat) => congrArg Nat.cast (Nat.div_one _)
  | -[_+1]  => congrArg negSucc (Nat.div_one _)

@[simp] theorem emod_one (a : Int) : a % 1 = 0 := by
  simp [emod_def, Int.one_mul, Int.sub_self]

@[simp] protected theorem ediv_self {a : Int} (H : a ≠ 0) : a / a = 1 := by
  have := Int.mul_ediv_cancel 1 H; rwa [Int.one_mul] at this

@[simp]
theorem Int.emod_sub_cancel (x y : Int): (x - y)%y = x%y := by
  by_cases h : y = 0
  · simp [h]
  · simp only [Int.emod_def, Int.sub_ediv_of_dvd, Int.dvd_refl, Int.ediv_self h, Int.mul_sub]
    simp [Int.mul_one, Int.sub_sub, Int.add_comm y]

/-! bmod -/

@[simp] theorem bmod_emod : bmod x m % m = x % m := by
  dsimp [bmod]
  split <;> simp [Int.sub_emod]

@[simp]
theorem emod_bmod_congr (x : Int) (n : Nat) : Int.bmod (x%n) n = Int.bmod x n := by
  simp [bmod, Int.emod_emod]

theorem bmod_def (x : Int) (m : Nat) : bmod x m =
  if (x % m) < (m + 1) / 2 then
    x % m
  else
    (x % m) - m :=
  rfl

theorem bmod_pos (x : Int) (m : Nat) (p : x % m < (m + 1) / 2) : bmod x m = x % m := by
  simp [bmod_def, p]

theorem bmod_neg (x : Int) (m : Nat) (p : x % m ≥ (m + 1) / 2) : bmod x m = (x % m) - m := by
  simp [bmod_def, Int.not_lt.mpr p]

@[simp]
theorem bmod_one_is_zero (x : Int) : Int.bmod x 1 = 0 := by
  simp [Int.bmod]

@[simp]
theorem bmod_add_cancel (x : Int) (n : Nat) : Int.bmod (x + n) n = Int.bmod x n := by
  simp [bmod_def]

@[simp]
theorem bmod_add_mul_cancel (x : Int) (n : Nat) (k : Int) : Int.bmod (x + n * k) n = Int.bmod x n := by
  simp [bmod_def]

@[simp]
theorem bmod_sub_cancel (x : Int) (n : Nat) : Int.bmod (x - n) n = Int.bmod x n := by
  simp [bmod_def]

@[simp]
theorem emod_add_bmod_congr (x : Int) (n : Nat) : Int.bmod (x%n + y) n = Int.bmod (x + y) n := by
  simp [Int.emod_def, Int.sub_eq_add_neg]
  rw [←Int.mul_neg, Int.add_right_comm,  Int.bmod_add_mul_cancel]

@[simp]
theorem bmod_add_bmod_congr : Int.bmod (Int.bmod x n + y) n = Int.bmod (x + y) n := by
  rw [bmod_def x n]
  split
  case inl p =>
    simp
  case inr p =>
    rw [Int.sub_eq_add_neg, Int.add_right_comm, ←Int.sub_eq_add_neg]
    simp

@[simp]
theorem add_bmod_bmod : Int.bmod (x + Int.bmod y n) n = Int.bmod (x + y) n := by
  rw [Int.add_comm x, Int.bmod_add_bmod_congr, Int.add_comm y]
