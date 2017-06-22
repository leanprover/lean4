/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro

Definitions and properties of gcd, lcm, and coprime.
-/
prelude
import init.data.nat.lemmas init.wf

open well_founded

namespace nat

/- gcd -/

def gcd.F : Π (y : ℕ), (Π (y' : ℕ), y' < y → nat → nat) → nat → nat
| 0        f x := x
| (succ y) f x := f (x % succ y) (mod_lt _ $ succ_pos _) (succ y)

def gcd (x y : nat) := fix lt_wf gcd.F y x

@[simp] theorem gcd_zero_right (x : nat) : gcd x 0 = x := congr_fun (fix_eq lt_wf gcd.F 0) x

@[simp] theorem gcd_succ (x y : nat) : gcd x (succ y) = gcd (succ y) (x % succ y) :=
congr_fun (fix_eq lt_wf gcd.F (succ y)) x

theorem gcd_one_right (n : ℕ) : gcd n 1 = 1 :=
eq.trans (gcd_succ n 0) (by rw [mod_one, gcd_zero_right])

theorem gcd_def (x : ℕ) : Π (y : ℕ), gcd x y = if y = 0 then x else gcd y (x % y)
| 0        := gcd_zero_right _
| (succ y) := (gcd_succ x y).trans (if_neg (succ_ne_zero y)).symm

theorem gcd_self : Π (n : ℕ), gcd n n = n
| 0         := gcd_zero_right _
| (succ n₁) := (gcd_succ (succ n₁) n₁).trans (by rw [mod_self, gcd_zero_right])

theorem gcd_zero_left : Π (n : ℕ), gcd 0 n = n
| 0         := gcd_zero_right _
| (succ n₁) := (gcd_succ 0 n₁).trans (by rw [zero_mod, gcd_zero_right])

theorem gcd_rec (m : ℕ) : Π (n : ℕ), gcd m n = gcd n (m % n)
| 0         := by rw [mod_zero, gcd_zero_left, gcd_zero_right]
| (succ n₁) := gcd_succ _ _

@[elab_as_eliminator]
theorem gcd.induction {P : ℕ → ℕ → Prop}
                   (m n : ℕ)
                   (H0 : ∀m, P m 0)
                   (H1 : ∀m n, 0 < n → P n (m % n) → P m n) :
                 P m n :=
@induction _ _ lt_wf (λn, ∀m, P m n) n (λk IH,
  by {induction k with k ih, exact H0,
      exact λm, H1 _ _ (succ_pos _) (IH _ (mod_lt _ (succ_pos _)) _)}) m

def lcm (m n : ℕ) : ℕ := m * n / (gcd m n)

@[reducible] def coprime (m n : ℕ) : Prop := gcd m n = 1

end nat