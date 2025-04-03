/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Markus Himmel
-/
prelude
import Init.Data.Nat.Dvd
import Init.NotationExtra
import Init.RCases

namespace Nat

/--
Computes the greatest common divisor of two natural numbers. The GCD of two natural numbers is the
largest natural number that evenly divides both.

In particular, the GCD of a number and `0` is the number itself.

This reference implementation via the Euclidean algorithm is overridden in both the kernel and the
compiler to efficiently evaluate using arbitrary-precision arithmetic. The definition provided here
is the logical model.

Examples:
* `Nat.gcd 10 15 = 5`
* `Nat.gcd 0 5 = 5`
* `Nat.gcd 7 0 = 7`
-/
@[extern "lean_nat_gcd"]
def gcd (m n : @& Nat) : Nat :=
  if m = 0 then
    n
  else
    gcd (n % m) m
  termination_by m
  decreasing_by simp_wf; apply mod_lt _ (zero_lt_of_ne_zero _); assumption

@[simp] theorem gcd_zero_left (y : Nat) : gcd 0 y = y := by
  rw [gcd]; rfl

theorem gcd_succ (x y : Nat) : gcd (succ x) y = gcd (y % succ x) (succ x) := by
  rw [gcd]; rfl

theorem gcd_add_one (x y : Nat) : gcd (x + 1) y = gcd (y % (x + 1)) (x + 1) := by
  rw [gcd]; rfl

theorem gcd_def (x y : Nat) : gcd x y = if x = 0 then y else gcd (y % x) x := by
  cases x <;> simp [Nat.gcd_add_one]

@[simp] theorem gcd_one_left (n : Nat) : gcd 1 n = 1 := by
  rw [gcd_succ, mod_one]
  rfl

@[simp] theorem gcd_zero_right (n : Nat) : gcd n 0 = n := by
  cases n with
  | zero => simp [gcd_succ]
  | succ n =>
    -- `simp [gcd_succ]` produces an invalid term unless `gcd_succ` is proved with `id rfl` instead
    rw [gcd_succ]
    exact gcd_zero_left _
instance : Std.LawfulIdentity gcd 0 where
  left_id := gcd_zero_left
  right_id := gcd_zero_right

@[simp] theorem gcd_self (n : Nat) : gcd n n = n := by
  cases n <;> simp [gcd_succ]
instance : Std.IdempotentOp gcd := ⟨gcd_self⟩

theorem gcd_rec (m n : Nat) : gcd m n = gcd (n % m) m :=
  match m with
  | 0 => by have := (mod_zero n).symm; rwa [gcd, gcd_zero_right]
  | _ + 1 => by simp [gcd_succ]

@[elab_as_elim] theorem gcd.induction {P : Nat → Nat → Prop} (m n : Nat)
    (H0 : ∀n, P 0 n) (H1 : ∀ m n, 0 < m → P (n % m) m → P m n) : P m n :=
  Nat.strongRecOn (motive := fun m => ∀ n, P m n) m
    (fun
    | 0, _ => H0
    | _+1, IH => fun _ => H1 _ _ (succ_pos _) (IH _ (mod_lt _ (succ_pos _)) _) )
    n

theorem gcd_dvd (m n : Nat) : (gcd m n ∣ m) ∧ (gcd m n ∣ n) := by
  induction m, n using gcd.induction with
  | H0 n => rw [gcd_zero_left]; exact ⟨Nat.dvd_zero n, Nat.dvd_refl n⟩
  | H1 m n _ IH => rw [← gcd_rec] at IH; exact ⟨IH.2, (dvd_mod_iff IH.2).1 IH.1⟩

theorem gcd_dvd_left (m n : Nat) : gcd m n ∣ m := (gcd_dvd m n).left

theorem gcd_dvd_right (m n : Nat) : gcd m n ∣ n := (gcd_dvd m n).right

theorem gcd_le_left (n) (h : 0 < m) : gcd m n ≤ m := le_of_dvd h <| gcd_dvd_left m n

theorem gcd_le_right (n) (h : 0 < n) : gcd m n ≤ n := le_of_dvd h <| gcd_dvd_right m n

theorem dvd_gcd : k ∣ m → k ∣ n → k ∣ gcd m n := by
  induction m, n using gcd.induction with intro km kn
  | H0 n => rw [gcd_zero_left]; exact kn
  | H1 n m _ IH => rw [gcd_rec]; exact IH ((dvd_mod_iff km).2 kn) km

theorem dvd_gcd_iff : k ∣ gcd m n ↔ k ∣ m ∧ k ∣ n :=
  ⟨fun h => let ⟨h₁, h₂⟩ := gcd_dvd m n; ⟨Nat.dvd_trans h h₁, Nat.dvd_trans h h₂⟩,
   fun ⟨h₁, h₂⟩ => dvd_gcd h₁ h₂⟩

theorem gcd_comm (m n : Nat) : gcd m n = gcd n m :=
  Nat.dvd_antisymm
    (dvd_gcd (gcd_dvd_right m n) (gcd_dvd_left m n))
    (dvd_gcd (gcd_dvd_right n m) (gcd_dvd_left n m))
instance : Std.Commutative gcd := ⟨gcd_comm⟩

theorem gcd_eq_left_iff_dvd : gcd m n = m ↔ m ∣ n :=
  ⟨fun h => h ▸ gcd_dvd_right m n,
   fun h => by rw [gcd_rec, mod_eq_zero_of_dvd h, gcd_zero_left]⟩

theorem gcd_eq_right_iff_dvd : gcd n m = m ↔ m ∣ n := by
  rw [gcd_comm]; exact gcd_eq_left_iff_dvd

theorem gcd_assoc (m n k : Nat) : gcd (gcd m n) k = gcd m (gcd n k) :=
  Nat.dvd_antisymm
    (dvd_gcd
      (Nat.dvd_trans (gcd_dvd_left (gcd m n) k) (gcd_dvd_left m n))
      (dvd_gcd (Nat.dvd_trans (gcd_dvd_left (gcd m n) k) (gcd_dvd_right m n))
        (gcd_dvd_right (gcd m n) k)))
    (dvd_gcd
      (dvd_gcd (gcd_dvd_left m (gcd n k))
        (Nat.dvd_trans (gcd_dvd_right m (gcd n k)) (gcd_dvd_left n k)))
      (Nat.dvd_trans (gcd_dvd_right m (gcd n k)) (gcd_dvd_right n k)))

@[simp] theorem gcd_one_right (n : Nat) : gcd n 1 = 1 := (gcd_comm n 1).trans (gcd_one_left n)

theorem gcd_mul_left (m n k : Nat) : gcd (m * n) (m * k) = m * gcd n k := by
  induction n, k using gcd.induction with
  | H0 k => simp
  | H1 n k _ IH => rwa [← mul_mod_mul_left, ← gcd_rec, ← gcd_rec] at IH

theorem gcd_mul_right (m n k : Nat) : gcd (m * n) (k * n) = gcd m k * n := by
  rw [Nat.mul_comm m n, Nat.mul_comm k n, Nat.mul_comm (gcd m k) n, gcd_mul_left]

theorem gcd_pos_of_pos_left {m : Nat} (n : Nat) (mpos : 0 < m) : 0 < gcd m n :=
  pos_of_dvd_of_pos (gcd_dvd_left m n) mpos

theorem gcd_pos_of_pos_right (m : Nat) {n : Nat} (npos : 0 < n) : 0 < gcd m n :=
  pos_of_dvd_of_pos (gcd_dvd_right m n) npos

theorem div_gcd_pos_of_pos_left (b : Nat) (h : 0 < a) : 0 < a / a.gcd b :=
  (Nat.le_div_iff_mul_le <| Nat.gcd_pos_of_pos_left _ h).2 (Nat.one_mul _ ▸ Nat.gcd_le_left _ h)

theorem div_gcd_pos_of_pos_right (a : Nat) (h : 0 < b) : 0 < b / a.gcd b :=
  (Nat.le_div_iff_mul_le <| Nat.gcd_pos_of_pos_right _ h).2 (Nat.one_mul _ ▸ Nat.gcd_le_right _ h)

theorem eq_zero_of_gcd_eq_zero_left {m n : Nat} (H : gcd m n = 0) : m = 0 :=
  match eq_zero_or_pos m with
  | .inl H0 => H0
  | .inr H1 => absurd (Eq.symm H) (ne_of_lt (gcd_pos_of_pos_left _ H1))

theorem eq_zero_of_gcd_eq_zero_right {m n : Nat} (H : gcd m n = 0) : n = 0 := by
  rw [gcd_comm] at H
  exact eq_zero_of_gcd_eq_zero_left H

theorem gcd_ne_zero_left : m ≠ 0 → gcd m n ≠ 0 := mt eq_zero_of_gcd_eq_zero_left

theorem gcd_ne_zero_right : n ≠ 0 → gcd m n ≠ 0 := mt eq_zero_of_gcd_eq_zero_right

theorem gcd_div {m n k : Nat} (H1 : k ∣ m) (H2 : k ∣ n) :
    gcd (m / k) (n / k) = gcd m n / k :=
  match eq_zero_or_pos k with
  | .inl H0 => by simp [H0]
  | .inr H3 => by
    apply Nat.eq_of_mul_eq_mul_right H3
    rw [Nat.div_mul_cancel (dvd_gcd H1 H2), ← gcd_mul_right,
        Nat.div_mul_cancel H1, Nat.div_mul_cancel H2]

theorem gcd_dvd_gcd_of_dvd_left {m k : Nat} (n : Nat) (H : m ∣ k) : gcd m n ∣ gcd k n :=
  dvd_gcd (Nat.dvd_trans (gcd_dvd_left m n) H) (gcd_dvd_right m n)

theorem gcd_dvd_gcd_of_dvd_right {m k : Nat} (n : Nat) (H : m ∣ k) : gcd n m ∣ gcd n k :=
  dvd_gcd (gcd_dvd_left n m) (Nat.dvd_trans (gcd_dvd_right n m) H)

theorem gcd_dvd_gcd_mul_left_left (m n k : Nat) : gcd m n ∣ gcd (k * m) n :=
  gcd_dvd_gcd_of_dvd_left _ (Nat.dvd_mul_left _ _)

@[deprecated gcd_dvd_gcd_mul_left_left (since := "2025-04-01")]
theorem gcd_dvd_gcd_mul_left (m n k : Nat) : gcd m n ∣ gcd (k * m) n :=
  gcd_dvd_gcd_mul_left_left m n k

theorem gcd_dvd_gcd_mul_right_left (m n k : Nat) : gcd m n ∣ gcd (m * k) n :=
  gcd_dvd_gcd_of_dvd_left _ (Nat.dvd_mul_right _ _)

@[deprecated gcd_dvd_gcd_mul_right_left (since := "2025-04-01")]
theorem gcd_dvd_gcd_mul_right (m n k : Nat) : gcd m n ∣ gcd (m * k) n :=
  gcd_dvd_gcd_mul_right_left m n k

theorem gcd_dvd_gcd_mul_left_right (m n k : Nat) : gcd m n ∣ gcd m (k * n) :=
  gcd_dvd_gcd_of_dvd_right _ (Nat.dvd_mul_left _ _)

theorem gcd_dvd_gcd_mul_right_right (m n k : Nat) : gcd m n ∣ gcd m (n * k) :=
  gcd_dvd_gcd_of_dvd_right _ (Nat.dvd_mul_right _ _)

theorem gcd_eq_left {m n : Nat} (H : m ∣ n) : gcd m n = m :=
  Nat.dvd_antisymm (gcd_dvd_left _ _) (dvd_gcd (Nat.dvd_refl _) H)

theorem gcd_eq_right {m n : Nat} (H : n ∣ m) : gcd m n = n := by
  rw [gcd_comm, gcd_eq_left H]

theorem gcd_right_eq_iff {m n n' : Nat} : gcd m n = gcd m n' ↔ ∀ k, k ∣ m → (k ∣ n ↔ k ∣ n') := by
  refine ⟨fun h k hkm => ⟨fun hkn => ?_, fun hkn' => ?_⟩, fun h => Nat.dvd_antisymm ?_ ?_⟩
  · exact Nat.dvd_trans (h ▸ dvd_gcd hkm hkn) (Nat.gcd_dvd_right m n')
  · exact Nat.dvd_trans (h ▸ dvd_gcd hkm hkn') (Nat.gcd_dvd_right m n)
  · exact dvd_gcd_iff.2 ⟨gcd_dvd_left _ _, (h _ (gcd_dvd_left _ _)).1 (gcd_dvd_right _ _)⟩
  · exact dvd_gcd_iff.2 ⟨gcd_dvd_left _ _, (h _ (gcd_dvd_left _ _)).2 (gcd_dvd_right _ _)⟩

theorem gcd_left_eq_iff {m m' n : Nat} : gcd m n = gcd m' n ↔ ∀ k, k ∣ n → (k ∣ m ↔ k ∣ m') := by
  rw [gcd_comm m n, gcd_comm m' n, gcd_right_eq_iff]

@[simp] theorem gcd_mul_left_left (m n : Nat) : gcd (m * n) n = n :=
  Nat.dvd_antisymm (gcd_dvd_right _ _) (dvd_gcd (Nat.dvd_mul_left _ _) (Nat.dvd_refl _))

@[simp] theorem gcd_mul_left_right (m n : Nat) : gcd n (m * n) = n := by
  rw [gcd_comm, gcd_mul_left_left]

@[simp] theorem gcd_mul_right_left (m n : Nat) : gcd (n * m) n = n := by
  rw [Nat.mul_comm, gcd_mul_left_left]

@[simp] theorem gcd_mul_right_right (m n : Nat) : gcd n (n * m) = n := by
  rw [gcd_comm, gcd_mul_right_left]

@[simp] theorem gcd_gcd_self_right_left (m n : Nat) : gcd m (gcd m n) = gcd m n :=
  Nat.dvd_antisymm (gcd_dvd_right _ _) (dvd_gcd (gcd_dvd_left _ _) (Nat.dvd_refl _))

@[simp] theorem gcd_gcd_self_right_right (m n : Nat) : gcd m (gcd n m) = gcd n m := by
  rw [gcd_comm n m, gcd_gcd_self_right_left]

@[simp] theorem gcd_gcd_self_left_right (m n : Nat) : gcd (gcd n m) m = gcd n m := by
  rw [gcd_comm, gcd_gcd_self_right_right]

@[simp] theorem gcd_gcd_self_left_left (m n : Nat) : gcd (gcd m n) m = gcd m n := by
  rw [gcd_comm m n, gcd_gcd_self_left_right]

@[simp] theorem gcd_add_mul_right_right (m n k : Nat) : gcd m (n + k * m) = gcd m n := by
  simp [gcd_rec m (n + k * m), gcd_rec m n]

@[deprecated gcd_add_mul_right_right (since := "2025-03-31")]
theorem gcd_add_mul_self (m n k : Nat) : gcd m (n + k * m) = gcd m n :=
  gcd_add_mul_right_right _ _ _

@[simp] theorem gcd_add_mul_left_right (m n k : Nat) : gcd m (n + m * k) = gcd m n := by
  rw [Nat.mul_comm, gcd_add_mul_right_right]

@[simp] theorem gcd_mul_right_add_right (m n k : Nat) : gcd m (k * m + n) = gcd m n := by
  rw [Nat.add_comm, gcd_add_mul_right_right]

@[simp] theorem gcd_mul_left_add_right (m n k : Nat) : gcd m (m * k + n) = gcd m n := by
  rw [Nat.add_comm, gcd_add_mul_left_right]

@[simp] theorem gcd_add_mul_right_left (m n k : Nat) : gcd (n + k * m) m = gcd n m := by
  rw [gcd_comm, gcd_add_mul_right_right, gcd_comm]

@[simp] theorem gcd_add_mul_left_left (m n k : Nat) : gcd (n + m * k) m = gcd n m := by
  rw [Nat.mul_comm, gcd_add_mul_right_left]

@[simp] theorem gcd_mul_right_add_left (m n k : Nat) : gcd (k * m + n) m = gcd n m := by
  rw [Nat.add_comm, gcd_add_mul_right_left]

@[simp] theorem gcd_mul_left_add_left (m n k : Nat) : gcd (m * k + n) m = gcd n m := by
  rw [Nat.add_comm, gcd_add_mul_left_left]

@[simp] theorem gcd_add_self_right (m n : Nat) : gcd m (n + m) = gcd m n := by
  simpa using gcd_add_mul_right_right _ _ 1

@[simp] theorem gcd_self_add_right (m n : Nat) : gcd m (m + n) = gcd m n := by
  simpa using gcd_mul_right_add_right _ _ 1

@[simp] theorem gcd_add_self_left (m n : Nat) : gcd (n + m) m = gcd n m := by
  simpa using gcd_add_mul_right_left _ _ 1

@[simp] theorem gcd_self_add_left (m n : Nat) : gcd (m + n) m = gcd n m := by
  simpa using gcd_mul_right_add_left _ _ 1

@[simp] theorem gcd_add_left_left_of_dvd {m k : Nat} (n : Nat) :
    m ∣ k → gcd (k + n) m = gcd n m := by
  rintro ⟨l, rfl⟩; exact gcd_mul_left_add_left m n l

@[simp] theorem gcd_add_right_left_of_dvd {m k : Nat} (n : Nat) :
    m ∣ k → gcd (n + k) m = gcd n m := by
  rintro ⟨l, rfl⟩; exact gcd_add_mul_left_left m n l

@[simp] theorem gcd_add_left_right_of_dvd {n k : Nat} (m : Nat) :
    n ∣ k → gcd n (k + m) = gcd n m := by
  rintro ⟨l, rfl⟩; exact gcd_mul_left_add_right n m l

@[simp] theorem gcd_add_right_right_of_dvd {n k : Nat} (m : Nat) :
    n ∣ k → gcd n (m + k) = gcd n m := by
  rintro ⟨l, rfl⟩; exact gcd_add_mul_left_right n m l

@[simp] theorem gcd_sub_mul_right_right {m n k : Nat} (h : k * m ≤ n) :
    gcd m (n - k * m) = gcd m n := by
  rw [← gcd_add_mul_right_right m (n - k * m) k, Nat.sub_add_cancel h]

@[simp] theorem gcd_sub_mul_left_right {m n k : Nat} (h : m * k ≤ n) :
    gcd m (n - m * k) = gcd m n := by
  rw [← gcd_add_mul_left_right m (n - m * k) k, Nat.sub_add_cancel h]

@[simp] theorem gcd_mul_right_sub_right {m n k : Nat} (h : n ≤ k * m) :
    gcd m (k * m - n) = gcd m n :=
  gcd_right_eq_iff.2 fun _ hl => dvd_sub_iff_right h (Nat.dvd_mul_left_of_dvd hl _)

@[simp] theorem gcd_mul_left_sub_right {m n k : Nat} (h : n ≤ m * k) :
    gcd m (m * k - n) = gcd m n := by
  rw [Nat.mul_comm, gcd_mul_right_sub_right (Nat.mul_comm _ _ ▸ h)]

@[simp] theorem gcd_sub_mul_right_left {m n k : Nat} (h : k * m ≤ n) :
    gcd (n - k * m) m = gcd n m := by
  rw [gcd_comm, gcd_sub_mul_right_right h, gcd_comm]

@[simp] theorem gcd_sub_mul_left_left {m n k : Nat} (h : m * k ≤ n) :
    gcd (n - m * k) m = gcd n m := by
  rw [Nat.mul_comm, gcd_sub_mul_right_left (Nat.mul_comm _ _ ▸ h)]

@[simp] theorem gcd_mul_right_sub_left {m n k : Nat} (h : n ≤ k * m) :
    gcd (k * m - n) m = gcd n m := by
  rw [gcd_comm, gcd_mul_right_sub_right h, gcd_comm]

@[simp] theorem gcd_mul_left_sub_left {m n k : Nat} (h : n ≤ m * k) :
    gcd (m * k - n) m = gcd n m := by
  rw [Nat.mul_comm, gcd_mul_right_sub_left (Nat.mul_comm _ _ ▸ h)]

@[simp] theorem gcd_sub_self_right {m n : Nat} (h : m ≤ n) : gcd m (n - m) = gcd m n := by
  simpa using gcd_sub_mul_right_right (k := 1) (by simpa using h)

@[simp] theorem gcd_self_sub_right {m n : Nat} (h : n ≤ m) : gcd m (m - n) = gcd m n := by
  simpa using gcd_mul_right_sub_right (k := 1) (by simpa using h)

@[simp] theorem gcd_sub_self_left {m n : Nat} (h : m ≤ n) : gcd (n - m) m = gcd n m := by
  simpa using gcd_sub_mul_right_left (k := 1) (by simpa using h)

@[simp] theorem gcd_self_sub_left {m n : Nat} (h : n ≤ m) : gcd (m - n) m = gcd n m := by
  simpa using gcd_mul_right_sub_left (k := 1) (by simpa using h)

@[simp] theorem gcd_sub_left_left_of_dvd {n k : Nat} (m : Nat) (h : n ≤ k) :
    m ∣ k → gcd (k - n) m = gcd n m := by
  rintro ⟨l, rfl⟩; exact gcd_mul_left_sub_left h

@[simp] theorem gcd_sub_right_left_of_dvd {n k : Nat} (m : Nat) (h : k ≤ n) :
    m ∣ k → gcd (n - k) m = gcd n m := by
  rintro ⟨l, rfl⟩; exact gcd_sub_mul_left_left h

@[simp] theorem gcd_sub_left_right_of_dvd {m k : Nat} (n : Nat) (h : m ≤ k) :
    n ∣ k → gcd n (k - m) = gcd n m := by
  rintro ⟨l, rfl⟩; exact gcd_mul_left_sub_right h

@[simp] theorem gcd_sub_right_right_of_dvd {m k : Nat} (n : Nat) (h : k ≤ m) :
    n ∣ k → gcd n (m - k) = gcd n m := by
  rintro ⟨l, rfl⟩; exact gcd_sub_mul_left_right h

@[simp] theorem gcd_eq_zero_iff {i j : Nat} : gcd i j = 0 ↔ i = 0 ∧ j = 0 :=
  ⟨fun h => ⟨eq_zero_of_gcd_eq_zero_left h, eq_zero_of_gcd_eq_zero_right h⟩,
   fun h => by simp [h]⟩

/-- Characterization of the value of `Nat.gcd`. -/
theorem gcd_eq_iff {a b : Nat} :
    gcd a b = g ↔ g ∣ a ∧ g ∣ b ∧ (∀ c, c ∣ a → c ∣ b → c ∣ g) := by
  constructor
  · rintro rfl
    exact ⟨gcd_dvd_left _ _, gcd_dvd_right _ _, fun _ => Nat.dvd_gcd⟩
  · rintro ⟨ha, hb, hc⟩
    apply Nat.dvd_antisymm
    · apply hc
      · exact gcd_dvd_left a b
      · exact gcd_dvd_right a b
    · exact Nat.dvd_gcd ha hb

/-- Represent a divisor of `m * n` as a product of a divisor of `m` and a divisor of `n`. -/
def dvdProdDvdOfDvdProd {k m n : Nat} (h : k ∣ m * n) :
    {d : {m' // m' ∣ m} × {n' // n' ∣ n} // k = d.1.val * d.2.val} :=
  if h0 : gcd k m = 0 then
    ⟨⟨⟨0, eq_zero_of_gcd_eq_zero_right h0 ▸ Nat.dvd_refl 0⟩,
      ⟨n, Nat.dvd_refl n⟩⟩,
      eq_zero_of_gcd_eq_zero_left h0 ▸ (Nat.zero_mul n).symm⟩
  else by
    have hd : gcd k m * (k / gcd k m) = k := Nat.mul_div_cancel' (gcd_dvd_left k m)
    refine ⟨⟨⟨gcd k m, gcd_dvd_right k m⟩, ⟨k / gcd k m, ?_⟩⟩, hd.symm⟩
    apply Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero h0)
    rw [hd, ← gcd_mul_right]
    exact Nat.dvd_gcd (Nat.dvd_mul_right _ _) h

@[inherit_doc dvdProdDvdOfDvdProd, deprecated dvdProdDvdOfDvdProd (since := "2025-04-01")]
def prod_dvd_and_dvd_of_dvd_prod {k m n : Nat} (H : k ∣ m * n) :
    {d : {m' // m' ∣ m} × {n' // n' ∣ n} // k = d.1.val * d.2.val} :=
  dvdProdDvdOfDvdProd H

protected theorem dvd_mul {k m n : Nat} : k ∣ m * n ↔ ∃ k₁ k₂, k₁ ∣ m ∧ k₂ ∣ n ∧ k₁ * k₂ = k := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨⟨⟨k₁, hk₁⟩, ⟨k₂, hk₂⟩⟩, rfl⟩ := dvdProdDvdOfDvdProd h
    exact ⟨k₁, k₂, hk₁, hk₂, rfl⟩
  · rintro ⟨k₁, k₂, hk₁, hk₂, rfl⟩
    exact Nat.mul_dvd_mul hk₁ hk₂

theorem gcd_mul_right_dvd_mul_gcd (k m n : Nat) : gcd k (m * n) ∣ gcd k m * gcd k n := by
  let ⟨⟨⟨m', hm'⟩, ⟨n', hn'⟩⟩, (h : gcd k (m * n) = m' * n')⟩ :=
    dvdProdDvdOfDvdProd <| gcd_dvd_right k (m * n)
  rw [h]
  have h' : m' * n' ∣ k := h ▸ gcd_dvd_left ..
  exact Nat.mul_dvd_mul
    (dvd_gcd (Nat.dvd_trans (Nat.dvd_mul_right m' n') h') hm')
    (dvd_gcd (Nat.dvd_trans (Nat.dvd_mul_left n' m') h') hn')

@[deprecated gcd_mul_right_dvd_mul_gcd (since := "2025-04-02")]
theorem gcd_mul_dvd_mul_gcd (k m n : Nat) : gcd k (m * n) ∣ gcd k m * gcd k n :=
  gcd_mul_right_dvd_mul_gcd k m n

theorem gcd_mul_left_dvd_mul_gcd (k m n : Nat) : gcd (m * n) k ∣ gcd m k * gcd n k := by
  simpa [gcd_comm, Nat.mul_comm] using gcd_mul_right_dvd_mul_gcd _ _ _

theorem dvd_gcd_mul_iff_dvd_mul {k n m : Nat} : k ∣ gcd k n * m ↔ k ∣ n * m := by
  refine ⟨(Nat.dvd_trans · <| Nat.mul_dvd_mul_right (k.gcd_dvd_right n) m), fun ⟨y, hy⟩ ↦ ?_⟩
  rw [← gcd_mul_right, hy, gcd_mul_left]
  exact Nat.dvd_mul_right k (gcd m y)

theorem dvd_mul_gcd_iff_dvd_mul {k n m : Nat} : k ∣ n * gcd k m ↔ k ∣ n * m := by
  rw [Nat.mul_comm, dvd_gcd_mul_iff_dvd_mul, Nat.mul_comm]

theorem dvd_gcd_mul_gcd_iff_dvd_mul {k n m : Nat} : k ∣ gcd k n * gcd k m ↔ k ∣ n * m := by
  rw [dvd_gcd_mul_iff_dvd_mul, dvd_mul_gcd_iff_dvd_mul]

theorem gcd_eq_one_iff {m n : Nat} : gcd m n = 1 ↔ ∀ c, c ∣ m → c ∣ n → c = 1 := by
  simp [gcd_eq_iff]

theorem gcd_mul_right_right_of_gcd_eq_one {n m k : Nat} : gcd n m = 1 → gcd n (m * k) = gcd n k := by
  rw [gcd_right_eq_iff, gcd_eq_one_iff]
  refine fun h l hl₁ => ⟨?_, fun a => Nat.dvd_mul_left_of_dvd a m⟩
  rw [Nat.dvd_mul]
  rintro ⟨k₁, k₂, hk₁, hk₂, rfl⟩
  obtain rfl : k₁ = 1 := h _ (Nat.dvd_trans (Nat.dvd_mul_right k₁ k₂) hl₁) hk₁
  simpa

theorem gcd_mul_left_right_of_gcd_eq_one {n m k : Nat} (h : gcd n m = 1) :
    gcd n (k * m) = gcd n k := by
  rw [Nat.mul_comm, gcd_mul_right_right_of_gcd_eq_one h]

theorem gcd_mul_right_left_of_gcd_eq_one {n m k : Nat} (h : gcd n m = 1) :
    gcd (n * k) m = gcd k m := by
  rw [gcd_comm, gcd_mul_right_right_of_gcd_eq_one (gcd_comm _ _ ▸ h), gcd_comm]

theorem gcd_mul_left_left_of_gcd_eq_one {n m k : Nat} (h : gcd n m = 1) :
    gcd (k * n) m = gcd k m := by
  rw [Nat.mul_comm, gcd_mul_right_left_of_gcd_eq_one h]

theorem gcd_pow_left_of_gcd_eq_one {k n m : Nat} (h : gcd n m = 1) : gcd (n ^ k) m = 1 := by
  induction k with
  | zero => simp [Nat.pow_zero]
  | succ k ih => rw [Nat.pow_succ, gcd_mul_left_left_of_gcd_eq_one h, ih]

theorem gcd_pow_right_of_gcd_eq_one {k n m : Nat} (h : gcd n m = 1) : gcd n (m ^ k) = 1 := by
  rw [gcd_comm, gcd_pow_left_of_gcd_eq_one (gcd_comm _ _ ▸ h)]

theorem pow_gcd_pow_of_gcd_eq_one {k l n m : Nat} (h : gcd n m = 1) : gcd (n ^ k) (m ^ l) = 1 :=
  gcd_pow_left_of_gcd_eq_one (gcd_pow_right_of_gcd_eq_one h)

theorem gcd_div_gcd_div_gcd_of_pos_left {n m : Nat} (h : 0 < n) :
    gcd (n / gcd n m) (m / gcd n m) = 1 := by
  rw [gcd_div (gcd_dvd_left _ _) (gcd_dvd_right _ _), Nat.div_self (gcd_pos_of_pos_left _ h)]

theorem gcd_div_gcd_div_gcd_of_pos_right {n m : Nat} (h : 0 < m) :
    gcd (n / gcd n m) (m / gcd n m) = 1 := by
  rw [gcd_div (gcd_dvd_left _ _) (gcd_dvd_right _ _), Nat.div_self (gcd_pos_of_pos_right _ h)]

theorem pow_gcd_pow {k n m : Nat} : gcd (n ^ k) (m ^ k) = (gcd n m) ^ k := by
  refine (Nat.eq_zero_or_pos n).elim (by rintro rfl; cases k <;> simp [Nat.pow_zero]) (fun hn => ?_)
  conv => lhs; rw [← Nat.div_mul_cancel (gcd_dvd_left n m)]
  conv => lhs; arg 2; rw [← Nat.div_mul_cancel (gcd_dvd_right n m)]
  rw [Nat.mul_pow, Nat.mul_pow, gcd_mul_right, pow_gcd_pow_of_gcd_eq_one, Nat.one_mul]
  exact gcd_div_gcd_div_gcd_of_pos_left hn

theorem pow_dvd_pow_iff {a b n : Nat} (h : n ≠ 0) : a ^ n ∣ b ^ n ↔ a ∣ b := by
  rw [← gcd_eq_left_iff_dvd, ← gcd_eq_left_iff_dvd, pow_gcd_pow, Nat.pow_left_inj h]

end Nat
