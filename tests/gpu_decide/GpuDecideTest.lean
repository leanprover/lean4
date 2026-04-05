/-
Copyright (c) 2026 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tehlikeli107

Tests for the GPU-accelerated `decide` tactic (via GpuDecide).

Note: `gpu_decide` replaces `decide` via @[builtin_tactic],
so these tests use `decide` which routes through the GPU handler.
-/

import Lean.Elab.Tactic.GpuDecide

open Lean Meta

/-- Test: simple Nat equality -/
example : (2 + 2 : Nat) = 4 := by
  decide

/-- Test: simple Bool expression -/
example : true = true := by
  decide

/-- Test: Nat comparison -/
example : (10 : Nat) > 5 := by
  decide

/-- Test: multiple Nat operations -/
example : (3 * 4 + 2 : Nat) = 14 := by
  decide

/-- Test: bit-level operations -/
example : (0b1010 : Nat) = 10 := by
  decide

/-- Test: Nat subtraction -/
example : (100 - 37 : Nat) = 63 := by
  decide

/-- Test: Nat power -/
example : (2 ^ 10 : Nat) = 1024 := by
  decide

/-- Test: complex Bool expression -/
example : (true || false) = true := by
  decide

/-- Test: Nat divisibility -/
example : (12 % 3 : Nat) = 0 := by
  decide

/-- Test: multiple comparisons -/
example : (5 : Nat) < 10 := by
  decide
