/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Nat.Div

namespace Nat

private def gcdF (x : Nat) : (∀ x₁, x₁ < x → Nat → Nat) → Nat → Nat :=
  match x with
  | 0      => fun _ y => y
  | succ x => fun f y => f (y % succ x) (mod_lt _ (zero_lt_succ  _)) (succ x)

@[extern "lean_nat_gcd"]
def gcd (a b : @& Nat) : Nat :=
  WellFounded.fix lt_wf gcdF a b

@[simp] theorem gcd_zero_left (y : Nat) : gcd 0 y = y :=
  rfl

theorem gcd_succ (x y : Nat) : gcd (succ x) y = gcd (y % succ x) (succ x) :=
  rfl

@[simp] theorem gcd_one_left (n : Nat) : gcd 1 n = 1 := by
  rw [gcd_succ, mod_one]
  rfl

@[simp] theorem gcd_zero_right (n : Nat) : gcd n 0 = n := by
  cases n <;> simp [gcd_succ]

@[simp] theorem gcd_self (n : Nat) : gcd n n = n := by
  cases n <;> simp [gcd_succ]

end Nat
