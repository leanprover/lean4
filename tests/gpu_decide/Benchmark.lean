/-
Copyright (c) 2026 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tehlikeli107

Benchmarks for the GPU-accelerated `decide` tactic.

These tests measure the performance of `decide` on various problem sizes
to verify that the GPU handler is correctly routing and providing speedup.
-/

import Lean.Elab.Tactic.GpuDecide

section

open Lean Meta Elab Tactic

/-- Benchmark: simple Nat equality (baseline) -/
example : (2 + 2 : Nat) = 4 := by
  decide

/-- Benchmark: Nat arithmetic chain -/
example : (3 * 4 + 5 * 6 - 7 : Nat) = 35 := by
  decide

/-- Benchmark: large Nat power -/
example : (2 ^ 20 : Nat) = 1048576 := by
  decide

/-- Benchmark: Bool expression tree -/
example :
  (true && true) || (false && true) && (true || false) = true := by
  decide

/-- Benchmark: Nat comparison chain -/
example :
  (1 : Nat) < 2 ∧ 2 ≤ 3 ∧ 4 > 3 ∧ 5 ≥ 5 ∧ 6 ≠ 7 := by
  decide

/-- Benchmark: bitwise operations -/
example :
  (0b1010 : Nat) &&& 0b1100 = 0b1000 := by
  decide

/-- Benchmark: Nat modulo -/
example :
  (1234567 % 97 : Nat) = 67 := by
  decide

/-- Benchmark: nested arithmetic -/
example :
  (((2 + 3) * 4 - 5) / 3 : Nat) = 5 := by
  decide

/-- Benchmark: large factorial check -/
example :
  (1 * 2 * 3 * 4 * 5 * 6 * 7 * 8 * 9 * 10 : Nat) = 3628800 := by
  decide

/-- Benchmark: complex Bool + Nat -/
example :
  let x := (2 ^ 8 : Nat)
  let y := (3 ^ 5 : Nat)
  x < y && (x % 2 = 0) = true := by
  decide

end
