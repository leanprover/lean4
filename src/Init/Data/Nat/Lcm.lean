/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Markus Himmel
-/
prelude
import Init.Data.Nat.Gcd
import Init.Data.Nat.Lemmas

/-!
# Lemmas about `Nat.lcm`

-/

namespace Nat

/--
The least common multiple of `m` and `n` is the smallest natural number that's evenly divisible by
both `m` and `n`. Returns `0` if either `m` or `n` is `0`.

Examples:
 * `Nat.lcm 9 6 = 18`
 * `Nat.lcm 9 3 = 9`
 * `Nat.lcm 0 3 = 0`
 * `Nat.lcm 3 0 = 0`
-/
def lcm (m n : Nat) : Nat := m * n / gcd m n

theorem lcm_eq_mul_div (m n : Nat) : lcm m n = m * n / gcd m n := rfl

@[simp] theorem gcd_mul_lcm (m n : Nat) : gcd m n * lcm m n = m * n := by
  rw [lcm_eq_mul_div,
    Nat.mul_div_cancel' (Nat.dvd_trans (gcd_dvd_left m n) (Nat.dvd_mul_right m n))]

@[simp] theorem lcm_mul_gcd (m n : Nat) : lcm m n * gcd m n = m * n := by
  simp [Nat.mul_comm]

@[simp] theorem lcm_dvd_mul (m n : Nat) : lcm m n ∣ m * n := ⟨gcd m n, by simp⟩

@[simp] theorem gcd_dvd_mul (m n : Nat) : gcd m n ∣ m * n := ⟨lcm m n, by simp⟩

@[simp] theorem lcm_le_mul {m n : Nat} (hm : 0 < m) (hn : 0 < n) : lcm m n ≤ m * n :=
  le_of_dvd (Nat.mul_pos hm hn) (lcm_dvd_mul _ _)

@[simp] theorem gcd_le_mul {m n : Nat} (hm : 0 < m) (hn : 0 < n) : gcd m n ≤ m * n :=
  le_of_dvd (Nat.mul_pos hm hn) (gcd_dvd_mul _ _)

theorem lcm_comm (m n : Nat) : lcm m n = lcm n m := by
  rw [lcm_eq_mul_div, lcm_eq_mul_div, Nat.mul_comm n m, gcd_comm n m]
instance : Std.Commutative lcm := ⟨lcm_comm⟩

@[simp] theorem lcm_zero_left (m : Nat) : lcm 0 m = 0 := by simp [lcm_eq_mul_div]

@[simp] theorem lcm_zero_right (m : Nat) : lcm m 0 = 0 := by simp [lcm_eq_mul_div]

@[simp] theorem lcm_one_left (m : Nat) : lcm 1 m = m := by simp [lcm_eq_mul_div]

@[simp] theorem lcm_one_right (m : Nat) : lcm m 1 = m := by simp [lcm_eq_mul_div]
instance : Std.LawfulIdentity lcm 1 where
  left_id := lcm_one_left
  right_id := lcm_one_right

@[simp] theorem lcm_self (m : Nat) : lcm m m = m := by
  match eq_zero_or_pos m with
  | .inl h => rw [h, lcm_zero_left]
  | .inr h => simp [lcm_eq_mul_div, Nat.mul_div_cancel _ h]
instance : Std.IdempotentOp lcm := ⟨lcm_self⟩

theorem dvd_lcm_left (m n : Nat) : m ∣ lcm m n :=
  ⟨n / gcd m n, by rw [← Nat.mul_div_assoc m (Nat.gcd_dvd_right m n), lcm_eq_mul_div]⟩

theorem dvd_lcm_right (m n : Nat) : n ∣ lcm m n := lcm_comm n m ▸ dvd_lcm_left n m

theorem lcm_ne_zero (hm : m ≠ 0) (hn : n ≠ 0) : lcm m n ≠ 0 := by
  intro h
  have h1 := gcd_mul_lcm m n
  rw [h, Nat.mul_zero] at h1
  match mul_eq_zero.1 h1.symm with
  | .inl hm1 => exact hm hm1
  | .inr hn1 => exact hn hn1

theorem lcm_pos : 0 < m → 0 < n → 0 < lcm m n := by
  simpa [← Nat.pos_iff_ne_zero] using lcm_ne_zero

theorem le_lcm_left (m : Nat) (hn : 0 < n) : m ≤ lcm m n :=
  (Nat.eq_zero_or_pos m).elim (by rintro rfl; simp)
    (fun hm => le_of_dvd (lcm_pos hm hn) (dvd_lcm_left m n))

theorem le_lcm_right (n : Nat) (hm : 0 < m)  : n ≤ lcm m n :=
  (Nat.eq_zero_or_pos n).elim (by rintro rfl; simp)
    (fun hn => le_of_dvd (lcm_pos hm hn) (dvd_lcm_right m n))

theorem lcm_dvd {m n k : Nat} (H1 : m ∣ k) (H2 : n ∣ k) : lcm m n ∣ k := by
  match eq_zero_or_pos k with
  | .inl h => rw [h]; exact Nat.dvd_zero _
  | .inr kpos =>
    apply Nat.dvd_of_mul_dvd_mul_left (gcd_pos_of_pos_left n (pos_of_dvd_of_pos H1 kpos))
    rw [gcd_mul_lcm, ← gcd_mul_right, Nat.mul_comm n k]
    exact dvd_gcd (Nat.mul_dvd_mul_left _ H2) (Nat.mul_dvd_mul_right H1 _)

theorem lcm_dvd_iff {m n k : Nat} : lcm m n ∣ k ↔ m ∣ k ∧ n ∣ k :=
  ⟨fun h => ⟨Nat.dvd_trans (dvd_lcm_left _ _) h, Nat.dvd_trans (dvd_lcm_right _ _) h⟩,
   fun ⟨hm, hn⟩ => lcm_dvd hm hn⟩

theorem lcm_eq_left_iff_dvd : lcm m n = m ↔ n ∣ m := by
  refine (Nat.eq_zero_or_pos m).elim (by rintro rfl; simp) (fun hm => ?_)
  rw [lcm_eq_mul_div, Nat.div_eq_iff_eq_mul_left (gcd_pos_of_pos_left _ hm) (gcd_dvd_mul _ _),
    Nat.mul_left_cancel_iff hm, Eq.comm, gcd_eq_right_iff_dvd]

theorem lcm_eq_right_iff_dvd : lcm m n = n ↔ m ∣ n := by
  rw [lcm_comm, lcm_eq_left_iff_dvd]

theorem lcm_assoc (m n k : Nat) : lcm (lcm m n) k = lcm m (lcm n k) :=
Nat.dvd_antisymm
  (lcm_dvd
    (lcm_dvd (dvd_lcm_left m (lcm n k))
      (Nat.dvd_trans (dvd_lcm_left n k) (dvd_lcm_right m (lcm n k))))
    (Nat.dvd_trans (dvd_lcm_right n k) (dvd_lcm_right m (lcm n k))))
  (lcm_dvd
    (Nat.dvd_trans (dvd_lcm_left m n) (dvd_lcm_left (lcm m n) k))
    (lcm_dvd (Nat.dvd_trans (dvd_lcm_right m n) (dvd_lcm_left (lcm m n) k))
      (dvd_lcm_right (lcm m n) k)))
instance : Std.Associative lcm := ⟨lcm_assoc⟩

theorem lcm_mul_left (m n k : Nat) : lcm (m * n) (m * k) = m * lcm n k := by
  refine (Nat.eq_zero_or_pos m).elim (by rintro rfl; simp) (fun hm => ?_)
  rw [lcm_eq_mul_div, gcd_mul_left,
    Nat.mul_div_assoc _ (Nat.mul_dvd_mul_left _ (gcd_dvd_right _ _)), Nat.mul_div_mul_left _ _ hm,
    lcm_eq_mul_div, Nat.mul_div_assoc _ (gcd_dvd_right _ _), Nat.mul_assoc]

theorem lcm_mul_right (m n k : Nat) : lcm (m * n) (k * n) = lcm m k * n := by
  rw [Nat.mul_comm _ n, Nat.mul_comm _ n, Nat.mul_comm _ n, lcm_mul_left]

theorem eq_zero_of_lcm_eq_zero (h : lcm m n = 0) : m = 0 ∨ n = 0 := by
  cases m <;> cases n <;> simp [lcm_ne_zero] at *

@[simp] theorem lcm_eq_zero_iff : lcm m n = 0 ↔ m = 0 ∨ n = 0 := by
  cases m <;> cases n <;> simp [lcm_ne_zero] at *

@[simp] theorem lcm_pos_iff : 0 < lcm m n ↔ 0 < m ∧ 0 < n := by
  simp only [Nat.pos_iff_ne_zero, ne_eq, lcm_eq_zero_iff, not_or]

theorem lcm_eq_iff {n m l : Nat} :
    lcm n m = l ↔ n ∣ l ∧ m ∣ l ∧ (∀ c, n ∣ c → m ∣ c → l ∣ c) := by
  refine ⟨?_, fun ⟨hn, hm, hl⟩ => Nat.dvd_antisymm (lcm_dvd hn hm) ?_⟩
  · rintro rfl
    exact ⟨dvd_lcm_left _ _, dvd_lcm_right _ _, fun _ => Nat.lcm_dvd⟩
  · exact hl _ (dvd_lcm_left _ _) (dvd_lcm_right _ _)

theorem lcm_div {m n k : Nat} (hkm : k ∣ m) (hkn : k ∣ n) : lcm (m / k) (n / k) = lcm m n / k := by
  refine (Nat.eq_zero_or_pos k).elim (by rintro rfl; simp) (fun hk => lcm_eq_iff.2
    ⟨Nat.div_dvd_div hkm (dvd_lcm_left m n), Nat.div_dvd_div hkn (dvd_lcm_right m n),
     fun c hc₁ hc₂ => ?_⟩)
  rw [div_dvd_iff_dvd_mul _ hk] at hc₁ hc₂ ⊢
  · exact lcm_dvd hc₁ hc₂
  · exact Nat.dvd_trans hkm (dvd_lcm_left _ _)
  · exact hkn
  · exact hkm

theorem lcm_dvd_lcm_of_dvd_left {m k : Nat} (n : Nat) (h : m ∣ k) : lcm m n ∣ lcm k n :=
  lcm_dvd (Nat.dvd_trans h (dvd_lcm_left _ _)) (dvd_lcm_right _ _)

theorem lcm_dvd_lcm_of_dvd_right {m k : Nat} (n : Nat) (h : m ∣ k) : lcm n m ∣ lcm n k :=
  lcm_dvd (dvd_lcm_left _ _) (Nat.dvd_trans h (dvd_lcm_right _ _))

theorem lcm_dvd_lcm_mul_left_left (m n k : Nat) : lcm m n ∣ lcm (k * m) n :=
  lcm_dvd_lcm_of_dvd_left _ (Nat.dvd_mul_left _ _)

theorem lcm_dvd_lcm_mul_right_left (m n k : Nat) : lcm m n ∣ lcm (m * k) n :=
  lcm_dvd_lcm_of_dvd_left _ (Nat.dvd_mul_right _ _)

theorem lcm_dvd_lcm_mul_left_right (m n k : Nat) : lcm m n ∣ lcm m (k * n) :=
  lcm_dvd_lcm_of_dvd_right _ (Nat.dvd_mul_left _ _)

theorem lcm_dvd_lcm_mul_right_right (m n k : Nat) : lcm m n ∣ lcm m (n * k) :=
  lcm_dvd_lcm_of_dvd_right _ (Nat.dvd_mul_right _ _)

theorem lcm_eq_left {m n : Nat} (h : n ∣ m) : lcm m n = m :=
  lcm_eq_left_iff_dvd.2 h

theorem lcm_eq_right {m n : Nat} (h : m ∣ n) : lcm m n = n :=
  lcm_eq_right_iff_dvd.2 h

@[simp] theorem lcm_mul_left_left (m n : Nat) : lcm (m * n) n = m * n := by
  simpa [lcm_eq_iff, Nat.dvd_mul_left] using fun _ h _ => h

@[simp] theorem lcm_mul_left_right (m n : Nat) : lcm n (m * n) = m * n := by
  simp [lcm_eq_iff, Nat.dvd_mul_left]

@[simp] theorem lcm_mul_right_left (m n : Nat) : lcm (n * m) n = n * m := by
  simpa [lcm_eq_iff, Nat.dvd_mul_right] using fun _ h _ => h

@[simp] theorem lcm_mul_right_right (m n : Nat) : lcm n (n * m) = n * m := by
  simp [lcm_eq_iff, Nat.dvd_mul_right]

@[simp] theorem lcm_lcm_self_right_left (m n : Nat) : lcm m (lcm m n) = lcm m n := by
  simp [← lcm_assoc]

@[simp] theorem lcm_lcm_self_right_right (m n : Nat) : lcm m (lcm n m) = lcm m n := by
  rw [lcm_comm n m, lcm_lcm_self_right_left]

@[simp] theorem lcm_lcm_self_left_left (m n : Nat) : lcm (lcm m n) m = lcm n m := by
  simp [lcm_comm]

@[simp] theorem lcm_lcm_self_left_right (m n : Nat) : lcm (lcm n m) m = lcm n m := by
  simp [lcm_comm]

theorem lcm_eq_mul_iff {m n : Nat} : lcm m n = m * n ↔ m = 0 ∨ n = 0 ∨ gcd m n = 1 := by
  rw [lcm_eq_mul_div, Nat.div_eq_self, Nat.mul_eq_zero, or_assoc]

@[simp] theorem lcm_eq_one_iff {m n : Nat} : lcm m n = 1 ↔ m = 1 ∧ n = 1 := by
  refine ⟨fun h => ⟨?_, ?_⟩, by rintro ⟨rfl, rfl⟩; simp⟩ <;>
    (apply Nat.eq_one_of_dvd_one; simp [← h, dvd_lcm_left, dvd_lcm_right])

theorem lcm_mul_right_dvd_mul_lcm (k m n : Nat) : lcm k (m * n) ∣ lcm k m * lcm k n :=
  lcm_dvd (Nat.dvd_mul_left_of_dvd (dvd_lcm_left _ _) _)
    (Nat.mul_dvd_mul (dvd_lcm_right _ _) (dvd_lcm_right _ _))

theorem lcm_mul_left_dvd_mul_lcm (k m n : Nat) : lcm (m * n) k ∣ lcm m k * lcm n k := by
  simpa [lcm_comm, Nat.mul_comm] using lcm_mul_right_dvd_mul_lcm _ _ _

theorem lcm_dvd_mul_self_left_iff_dvd_mul {k n m : Nat} : lcm k n ∣ k * m ↔ n ∣ k * m :=
  ⟨fun h => Nat.dvd_trans (dvd_lcm_right _ _) h, fun h => lcm_dvd (Nat.dvd_mul_right k m) h⟩

theorem lcm_dvd_mul_self_right_iff_dvd_mul {k m n : Nat} : lcm n k ∣ m * k ↔ n ∣ m * k := by
  rw [lcm_comm, Nat.mul_comm m, lcm_dvd_mul_self_left_iff_dvd_mul]

theorem lcm_mul_right_right_eq_mul_of_lcm_eq_mul {n m k : Nat} (h : lcm n m = n * m) :
    lcm n (m * k) = lcm n k * m := by
  rcases lcm_eq_mul_iff.1 h with (rfl|rfl|h) <;> try (simp; done)
  rw [Nat.mul_comm _ m, lcm_eq_mul_div, gcd_mul_right_right_of_gcd_eq_one h, Nat.mul_comm,
    Nat.mul_assoc, Nat.mul_comm k, Nat.mul_div_assoc _ (gcd_dvd_mul _ _), lcm_eq_mul_div]

theorem lcm_mul_left_right_eq_mul_of_lcm_eq_mul {n m k} (h : lcm n m = n * m) :
    lcm n (k * m) = lcm n k * m := by
  rw [Nat.mul_comm, lcm_mul_right_right_eq_mul_of_lcm_eq_mul h, Nat.mul_comm]

theorem lcm_mul_right_left_eq_mul_of_lcm_eq_mul {n m k} (h : lcm n m = n * m) :
    lcm (n * k) m = n * lcm k m := by
  rw [lcm_comm, lcm_mul_right_right_eq_mul_of_lcm_eq_mul, lcm_comm, Nat.mul_comm]
  rwa [lcm_comm, Nat.mul_comm]

theorem lcm_mul_left_left_eq_mul_of_lcm_eq_mul {n m k} (h : lcm n m = n * m) :
    lcm (k * n) m = n * lcm k m := by
  rw [Nat.mul_comm, lcm_mul_right_left_eq_mul_of_lcm_eq_mul h]

theorem pow_lcm_pow {k n m : Nat} : lcm (n ^ k) (m ^ k) = (lcm n m) ^ k := by
  rw [lcm_eq_mul_div, pow_gcd_pow, ← Nat.mul_pow, ← Nat.div_pow (gcd_dvd_mul _ _), lcm_eq_mul_div]

end Nat
