/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro

Definitions and properties of gcd, lcm, and coprime.
-/
prelude
import init.data.nat.lemmas init.meta.well_founded_tactics

open well_founded

namespace nat

/- gcd -/

def gcd : nat → nat → nat
| 0        y := y
| (succ x) y := have y % succ x < succ x, from mod_lt _ $ succ_pos _,
                gcd (y % succ x) (succ x)


@[simp] theorem gcd_zero_left (x : nat) : gcd 0 x = x := by simp [gcd]

@[simp] theorem gcd_succ (x y : nat) : gcd (succ x) y = gcd (y % succ x) (succ x) :=
by simp [gcd]

@[simp] theorem gcd_one_left (n : ℕ) : gcd 1 n = 1 := by simp [gcd]

theorem gcd_def (x y : ℕ) : gcd x y = if x = 0 then y else gcd (y % x) x :=
by cases x; simp [gcd, succ_ne_zero]

@[simp] theorem gcd_self (n : ℕ) : gcd n n = n :=
by cases n; simp [gcd, mod_self]

@[simp] theorem gcd_zero_right (n : ℕ) : gcd n 0 = n :=
by cases n; simp [gcd]

theorem gcd_rec (m n : ℕ) : gcd m n = gcd (n % m) m :=
by cases m; simp [gcd]

@[elab_as_eliminator]
theorem gcd.induction {P : ℕ → ℕ → Prop}
                   (m n : ℕ)
                   (H0 : ∀n, P 0 n)
                   (H1 : ∀m n, 0 < m → P (n % m) m → P m n) :
                 P m n :=
@induction _ _ lt_wf (λm, ∀n, P m n) m (λk IH,
  by {induction k with k ih, exact H0,
      exact λn, H1 _ _ (succ_pos _) (IH _ (mod_lt _ (succ_pos _)) _)}) n

def lcm (m n : ℕ) : ℕ := m * n / (gcd m n)

@[reducible] def coprime (m n : ℕ) : Prop := gcd m n = 1

end nat