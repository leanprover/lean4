/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
module

prelude
public import Init.Data.Nat.Linear

public section

namespace Nat

theorem log2_terminates : ∀ n, n ≥ 2 → n / 2 < n
  | 2, _ => by decide
  | 3, _ => by decide
  | n+4, _ => by
    rw [div_eq, if_pos]
    refine succ_lt_succ (Nat.lt_trans ?_ (lt_succ_self _))
    exact log2_terminates (n+2) (by simp)
    simp

/--
Base-two logarithm of natural numbers. Returns `⌊max 0 (log₂ n)⌋`.

This function is overridden at runtime with an efficient implementation. This definition is
the logical model.

Examples:
 * `Nat.log2 0 = 0`
 * `Nat.log2 1 = 0`
 * `Nat.log2 2 = 1`
 * `Nat.log2 4 = 2`
 * `Nat.log2 7 = 2`
 * `Nat.log2 8 = 3`
-/
@[extern "lean_nat_log2"]
def log2 (n : @& Nat) : Nat :=
  if n ≥ 2 then log2 (n / 2) + 1 else 0
decreasing_by exact log2_terminates _ ‹_›

theorem log2_le_self (n : Nat) : Nat.log2 n ≤ n := by
  unfold Nat.log2; split
  · next h =>
    have := log2_le_self (n / 2)
    exact Nat.lt_of_le_of_lt this (Nat.div_lt_self (Nat.le_of_lt h) (by decide))
  · apply Nat.zero_le
decreasing_by exact Nat.log2_terminates _ ‹_›
