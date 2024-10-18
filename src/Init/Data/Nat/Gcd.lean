/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
prelude
import Init.Data.Nat.Dvd
import Init.NotationExtra
import Init.RCases

namespace Nat

/--
Computes the greatest common divisor of two natural numbers.

This reference implementation via the Euclidean algorithm
is overridden in both the kernel and the compiler to efficiently
evaluate using the "bignum" representation (see `Nat`).
The definition provided here is the logical model
(and it is soundness-critical that they coincide).

The GCD of two natural numbers is the largest natural number
that divides both arguments.
In particular, the GCD of a number and `0` is the number itself:
```
example : Nat.gcd 10 15 = 5 := rfl
example : Nat.gcd 0 5 = 5 := rfl
example : Nat.gcd 7 0 = 7 := rfl
```
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

theorem gcd_eq_left_iff_dvd : m ∣ n ↔ gcd m n = m :=
  ⟨fun h => by rw [gcd_rec, mod_eq_zero_of_dvd h, gcd_zero_left],
   fun h => h ▸ gcd_dvd_right m n⟩

theorem gcd_eq_right_iff_dvd : m ∣ n ↔ gcd n m = m := by
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

theorem gcd_dvd_gcd_mul_left (m n k : Nat) : gcd m n ∣ gcd (k * m) n :=
  gcd_dvd_gcd_of_dvd_left _ (Nat.dvd_mul_left _ _)

theorem gcd_dvd_gcd_mul_right (m n k : Nat) : gcd m n ∣ gcd (m * k) n :=
  gcd_dvd_gcd_of_dvd_left _ (Nat.dvd_mul_right _ _)

theorem gcd_dvd_gcd_mul_left_right (m n k : Nat) : gcd m n ∣ gcd m (k * n) :=
  gcd_dvd_gcd_of_dvd_right _ (Nat.dvd_mul_left _ _)

theorem gcd_dvd_gcd_mul_right_right (m n k : Nat) : gcd m n ∣ gcd m (n * k) :=
  gcd_dvd_gcd_of_dvd_right _ (Nat.dvd_mul_right _ _)

theorem gcd_eq_left {m n : Nat} (H : m ∣ n) : gcd m n = m :=
  Nat.dvd_antisymm (gcd_dvd_left _ _) (dvd_gcd (Nat.dvd_refl _) H)

theorem gcd_eq_right {m n : Nat} (H : n ∣ m) : gcd m n = n := by
  rw [gcd_comm, gcd_eq_left H]

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

theorem gcd_add_mul_self (m n k : Nat) : gcd m (n + k * m) = gcd m n := by
  simp [gcd_rec m (n + k * m), gcd_rec m n]

theorem gcd_eq_zero_iff {i j : Nat} : gcd i j = 0 ↔ i = 0 ∧ j = 0 :=
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
def prod_dvd_and_dvd_of_dvd_prod {k m n : Nat} (H : k ∣ m * n) :
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
    exact Nat.dvd_gcd (Nat.dvd_mul_right _ _) H

theorem gcd_mul_dvd_mul_gcd (k m n : Nat) : gcd k (m * n) ∣ gcd k m * gcd k n := by
  let ⟨⟨⟨m', hm'⟩, ⟨n', hn'⟩⟩, (h : gcd k (m * n) = m' * n')⟩ :=
    prod_dvd_and_dvd_of_dvd_prod <| gcd_dvd_right k (m * n)
  rw [h]
  have h' : m' * n' ∣ k := h ▸ gcd_dvd_left ..
  exact Nat.mul_dvd_mul
    (dvd_gcd (Nat.dvd_trans (Nat.dvd_mul_right m' n') h') hm')
    (dvd_gcd (Nat.dvd_trans (Nat.dvd_mul_left n' m') h') hn')

end Nat
