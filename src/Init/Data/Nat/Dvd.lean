/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
prelude
import Init.Data.Nat.Div

namespace Nat

/--
Divisibility of natural numbers. `a ∣ b` (typed as `\|`) says that
there is some `c` such that `b = a * c`.
-/
instance : Dvd Nat where
  dvd a b := Exists (fun c => b = a * c)

protected theorem dvd_refl (a : Nat) : a ∣ a := ⟨1, by simp⟩

protected theorem dvd_zero (a : Nat) : a ∣ 0 := ⟨0, by simp⟩

protected theorem dvd_mul_left (a b : Nat) : a ∣ b * a := ⟨b, Nat.mul_comm b a⟩
protected theorem dvd_mul_right (a b : Nat) : a ∣ a * b := ⟨b, rfl⟩

protected theorem dvd_trans {a b c : Nat} (h₁ : a ∣ b) (h₂ : b ∣ c) : a ∣ c :=
  match h₁, h₂ with
  | ⟨d, (h₃ : b = a * d)⟩, ⟨e, (h₄ : c = b * e)⟩ =>
    ⟨d * e, show c = a * (d * e) by simp[h₃,h₄, Nat.mul_assoc]⟩

protected theorem eq_zero_of_zero_dvd {a : Nat} (h : 0 ∣ a) : a = 0 :=
  let ⟨c, H'⟩ := h; H'.trans c.zero_mul

@[simp] protected theorem zero_dvd {n : Nat} : 0 ∣ n ↔ n = 0 :=
  ⟨Nat.eq_zero_of_zero_dvd, fun h => h.symm ▸ Nat.dvd_zero 0⟩

protected theorem dvd_add {a b c : Nat} (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b + c :=
  let ⟨d, hd⟩ := h₁; let ⟨e, he⟩ := h₂; ⟨d + e, by simp [Nat.left_distrib, hd, he]⟩

protected theorem dvd_add_iff_right {k m n : Nat} (h : k ∣ m) : k ∣ n ↔ k ∣ m + n :=
  ⟨Nat.dvd_add h,
    match m, h with
    | _, ⟨d, rfl⟩ => fun ⟨e, he⟩ =>
      ⟨e - d, by rw [Nat.mul_sub_left_distrib, ← he, Nat.add_sub_cancel_left]⟩⟩

protected theorem dvd_add_iff_left {k m n : Nat} (h : k ∣ n) : k ∣ m ↔ k ∣ m + n := by
  rw [Nat.add_comm]; exact Nat.dvd_add_iff_right h

theorem dvd_mod_iff {k m n : Nat} (h: k ∣ n) : k ∣ m % n ↔ k ∣ m :=
  have := Nat.dvd_add_iff_left <| Nat.dvd_trans h <| Nat.dvd_mul_right n (m / n)
  by rwa [mod_add_div] at this

theorem le_of_dvd {m n : Nat} (h : 0 < n) : m ∣ n → m ≤ n
  | ⟨k, e⟩ => by
    revert h
    rw [e]
    match k with
    | 0 => intro hn; simp at hn
    | pk+1 =>
      intro
      have := Nat.mul_le_mul_left m (succ_pos pk)
      rwa [Nat.mul_one] at this

protected theorem dvd_antisymm : ∀ {m n : Nat}, m ∣ n → n ∣ m → m = n
  | _, 0, _, h₂ => Nat.eq_zero_of_zero_dvd h₂
  | 0, _, h₁, _ => (Nat.eq_zero_of_zero_dvd h₁).symm
  | _+1, _+1, h₁, h₂ => Nat.le_antisymm (le_of_dvd (succ_pos _) h₁) (le_of_dvd (succ_pos _) h₂)

theorem pos_of_dvd_of_pos {m n : Nat} (H1 : m ∣ n) (H2 : 0 < n) : 0 < m :=
  Nat.pos_of_ne_zero fun m0 => Nat.ne_of_gt H2 <| Nat.eq_zero_of_zero_dvd (m0 ▸ H1)

@[simp] protected theorem one_dvd (n : Nat) : 1 ∣ n := ⟨n, n.one_mul.symm⟩

theorem eq_one_of_dvd_one {n : Nat} (H : n ∣ 1) : n = 1 := Nat.dvd_antisymm H n.one_dvd

theorem mod_eq_zero_of_dvd {m n : Nat} (H : m ∣ n) : n % m = 0 := by
  let ⟨z, H⟩ := H; rw [H, mul_mod_right]

theorem dvd_of_mod_eq_zero {m n : Nat} (H : n % m = 0) : m ∣ n := by
  exists n / m
  have := (mod_add_div n m).symm
  rwa [H, Nat.zero_add] at this

theorem dvd_iff_mod_eq_zero (m n : Nat) : m ∣ n ↔ n % m = 0 :=
  ⟨mod_eq_zero_of_dvd, dvd_of_mod_eq_zero⟩

instance decidable_dvd : @DecidableRel Nat (·∣·) :=
  fun _ _ => decidable_of_decidable_of_iff (dvd_iff_mod_eq_zero _ _).symm

theorem emod_pos_of_not_dvd {a b : Nat} (h : ¬ a ∣ b) : 0 < b % a := by
  rw [dvd_iff_mod_eq_zero] at h
  exact Nat.pos_of_ne_zero h

protected theorem mul_div_cancel' {n m : Nat} (H : n ∣ m) : n * (m / n) = m := by
  have := mod_add_div m n
  rwa [mod_eq_zero_of_dvd H, Nat.zero_add] at this

protected theorem div_mul_cancel {n m : Nat} (H : n ∣ m) : m / n * n = m := by
  rw [Nat.mul_comm, Nat.mul_div_cancel' H]

end Nat
