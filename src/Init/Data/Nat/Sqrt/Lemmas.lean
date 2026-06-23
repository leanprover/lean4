/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

prelude
public import Init.Data.Nat.Sqrt.Basic
import all Init.Data.Nat.Sqrt.Basic
import Init.TacticsExtra
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Omega

public section

namespace Nat

/-!
### `sqrt`

See [Wikipedia, *Methods of computing square roots*]
(https://en.wikipedia.org/wiki/Methods_of_computing_square_roots#Binary_numeral_system_(base_2)).
-/

private theorem AM_GM : {a b : Nat} → (4 * a * b ≤ (a + b) * (a + b))
  | 0, _ => by rw [Nat.mul_zero, Nat.zero_mul]; exact zero_le _
  | _, 0 => by rw [Nat.mul_zero]; exact zero_le _
  | a + 1, b + 1 => by
    simpa only [Nat.mul_add, Nat.add_mul, show (4 : Nat) = 1 + 1 + 1 + 1 from rfl, Nat.one_mul,
      Nat.mul_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_le_add_iff_left]
      using Nat.add_le_add_right (@AM_GM a b) 4

private theorem sqrt.iter_sq_le (n guess : Nat) : sqrt.iter n guess * sqrt.iter n guess ≤ n := by
  unfold sqrt.iter
  let next := (guess + n / guess) / 2
  if h : next < guess then
    simpa only [next, dif_pos h] using sqrt.iter_sq_le n next
  else
    apply Nat.mul_le_of_le_div
    simp only
    split <;> omega

private theorem sqrt.lt_iter_succ_sq (n guess : Nat) (hn : n < (guess + 1) * (guess + 1)) :
    n < (sqrt.iter n guess + 1) * (sqrt.iter n guess + 1) := by
  unfold sqrt.iter
  -- m was `next`
  let m := (guess + n / guess) / 2
  dsimp
  split <;> rename_i h
  · suffices n < (m + 1) * (m + 1) by
      simpa only [dif_pos h] using sqrt.lt_iter_succ_sq n m this
    refine Nat.lt_of_mul_lt_mul_left ?_ (a := 4 * (guess * guess))
    apply Nat.lt_of_le_of_lt AM_GM
    rw [show (4 : Nat) = 2 * 2 from rfl]
    rw [Nat.mul_mul_mul_comm 2, Nat.mul_mul_mul_comm (2 * guess)]
    refine Nat.mul_self_lt_mul_self (?_ : _ < _ * ((_ / 2) + 1))
    rw [← add_div_right _ (by decide), Nat.mul_comm 2, Nat.mul_assoc,
      show guess + n / guess + 2 = (guess + n / guess + 1) + 1 from rfl]
    have aux_theorem {a : Nat} : a ≤ 2 * ((a + 1) / 2) := by omega
    refine Nat.lt_of_lt_of_le ?_ (Nat.mul_le_mul_left _ aux_theorem)
    rw [Nat.add_assoc, Nat.mul_add]
    exact Nat.add_lt_add_left (lt_mul_div_succ _ (Nat.lt_of_le_of_lt (Nat.zero_le m) h)) _
  · exact hn

private def IsSqrt (n q : Nat) : Prop :=
  q * q ≤ n ∧ n < (q + 1) * (q + 1)

/-
Sketch of proof:
Up to rounding, in terms of the definition of `sqrt.iter`,

* By AM-GM inequality, `next² ≥ n` giving one of the bounds.
* When we terminated, we have `guess ≥ next` from which we deduce the other bound `n ≥ next²`.

To turn this into a lean proof we need to manipulate, use properties of natural number division etc.
-/
private theorem sqrt_isSqrt (n : Nat) : IsSqrt n (sqrt n) := by
  match n with
  | 0 => simp [IsSqrt, sqrt]
  | 1 => simp [IsSqrt, sqrt]
  | n + 2 =>
    have h : ¬ (n + 2) ≤ 1 := by simp
    simp only [IsSqrt, sqrt, h, ite_false]
    refine ⟨sqrt.iter_sq_le _ _, sqrt.lt_iter_succ_sq _ _ ?_⟩
    simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul, Nat.mul_one, ← Nat.add_assoc]
    rw [Nat.lt_add_one_iff, Nat.add_assoc, ← Nat.mul_two]
    refine Nat.le_trans (Nat.le_of_eq (div_add_mod' (n + 2) 2).symm) ?_
    rw [show (n + 2) / 2 * 2 + (n + 2) % 2 = n + 2 by omega]
    simp only [shiftLeft_eq, Nat.one_mul]
    refine Nat.le_of_lt (Nat.le_trans lt_log2_self (le_add_right_of_le ?_))
    rw [← Nat.pow_add]
    apply Nat.pow_le_pow_right (by decide)
    omega

theorem sqrt_le (n : Nat) : sqrt n * sqrt n ≤ n := (sqrt_isSqrt n).left

theorem lt_succ_sqrt (n : Nat) : n < succ (sqrt n) * succ (sqrt n) := (sqrt_isSqrt n).right

end Nat
