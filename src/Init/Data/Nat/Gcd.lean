/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Nat.Dvd

namespace Nat

@[extern "lean_nat_gcd"]
def gcd (m n : @& Nat) : Nat :=
  if m = 0 then
    n
  else
    gcd (n % m) m
termination_by m
decreasing_by simp_wf; apply mod_lt _ (zero_lt_of_ne_zero _); assumption

@[simp] theorem gcd_zero_left (y : Nat) : gcd 0 y = y :=
  rfl

theorem gcd_succ (x y : Nat) : gcd (succ x) y = gcd (y % succ x) (succ x) :=
  rfl

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

@[simp] theorem gcd_self (n : Nat) : gcd n n = n := by
  cases n <;> simp [gcd_succ]

theorem gcd_rec (m n : Nat) : gcd m n = gcd (n % m) m :=
  match m with
  | 0 => by have := (mod_zero n).symm; rwa [gcd_zero_right]
  | _ + 1 => by simp [gcd_succ]

@[elab_as_elim] theorem gcd.induction {P : Nat → Nat → Prop} (m n : Nat)
    (H0 : ∀n, P 0 n) (H1 : ∀ m n, 0 < m → P (n % m) m → P m n) : P m n :=
  Nat.strongInductionOn (motive := fun m => ∀ n, P m n) m
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

end Nat
