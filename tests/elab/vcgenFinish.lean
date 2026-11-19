/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import Std.WP

/-!
`vcgen … with finish` internalises each branch before solving it: a dead `match` branch leaves no
metavariable (`f_group_finish`), and a lifted precondition reaches grind's E-graph (`eat_spec_finish`).
Initialisation internalises the hypotheses as well, so an inconsistent local context closes the goal
before the `vcgen` step runs.
-/

open Std.WP Lean.Order
set_option experimental.vcgen true
set_option linter.unusedVariables false

abbrev M := StateM (List Nat)

def g : M Nat := pure 0

def h : M Nat := do set (← get).tail; pure 0

@[spec] theorem h_spec (s0 : List Nat) :
    ⦃ fun s => s = s0 ⦄ h ⦃ fun r s => s = s0.tail ⦄ := by
  vcgen [h] with finish

def f : M Nat := do
  match ← get with
  | 0 :: cs => set cs; g
  | _       => h

theorem f_group_finish (e : Nat) (inner rest : List Nat)
    (hEi : ⦃ fun s => s = inner ⦄ g ⦃ fun r s => r = e ∧ s = rest ⦄) :
    ⦃ fun s => s = 0 :: inner ⦄ f ⦃ fun r s => r = e ∧ s = rest ⦄ := by
  rw [f]; vcgen [hEi] with finish

def eat : Nat → M Nat
  | 0 => pure 0
  | fuel + 1 => do
    match ← get with
    | x :: xs => set xs; let r ← eat fuel; pure (x + r)
    | []      => pure 0

theorem eat_spec_finish (s0 : List Nat) (fuel : Nat) (hfuel : s0.length < fuel) :
    ⦃ fun s => s = s0 ⦄ eat fuel ⦃ fun r s => r = s0.sum ∧ s = [] ⦄ := by
  induction fuel generalizing s0 with
  | zero => omega
  | succ fuel ih => vcgen [eat, ih] with finish

/-! An inconsistent local context closes the goal during initialisation, leaving nothing for the
`vcgen` step. The first example is the same goal without the contradictory hypothesis. -/

example : ⦃ True ⦄ (pure 3 : Id Nat) ⦃ fun r => r = 3 ⦄ := by
  vcgen

example (hFalse : false = true) : ⦃ True ⦄ (pure 3 : Id Nat) ⦃ fun r => r = 3 ⦄ := by
  vcgen

example (hFalse : False) : ⦃ True ⦄ (pure 3 : Id Nat) ⦃ fun r => r = 3 ⦄ := by
  vcgen

example (hFalse : false = true) : ⦃ True ⦄ (pure 3 : Id Nat) ⦃ fun r => r = 3 ⦄ := by
  vcgen with finish

/-! The postcondition `r = 41 ∧ s = 41` of `peek_spec` is split into the hypotheses `r = 41` and
`s = 41`. No spec matches `bump r`, so `vcgen` substitutes `r = 41`, and `bump_41` applies to
`bump 41`. `sym.debug` checks the `SymM` invariants of both steps. -/

set_option sym.debug true

def peek : StateM Nat Nat := get

@[spec] theorem peek_spec (n : Nat) : ⦃ fun s => s = n ⦄ peek ⦃ fun r s => r = n ∧ s = n ⦄ := by
  vcgen [peek] with finish

def bump (n : Nat) : StateM Nat Nat := pure (n + 1)

@[spec] theorem bump_41 : ⦃ fun s => s = 41 ⦄ bump 41 ⦃ fun r s => r = 42 ∧ s = 41 ⦄ := by
  vcgen [bump] with finish

example : ⦃ fun s => s = 41 ⦄ (do let r ← peek; bump r) ⦃ fun r s => r = 42 ∧ s = 41 ⦄ := by
  vcgen with finish

/-! `vcgen` rewrites with the hypothesis `r = 3` when no other hypothesis mentions `r`. In the first
VC, `r < 5` mentions `r`, so the target stays `r = 4`. In the second VC, the target `r = 4` becomes
`3 = 4`, which simplifies to `False`. The hypothesis `r = 3` stays. -/

def three : StateM Nat Nat := pure 3

@[spec] theorem three_spec : ⦃ fun _ => True ⦄ three ⦃ fun r _ => r < 5 ∧ r = 3 ⦄ := by
  vcgen [three] with finish

def threeEq : StateM Nat Nat := pure 3

@[spec] theorem threeEq_spec : ⦃ fun _ => True ⦄ threeEq ⦃ fun r _ => r = 3 ⦄ := by
  vcgen [threeEq] with finish

/--
trace: case vc1
s✝¹ a✝ s✝ : Nat
left✝ : a✝ < 5
right✝ : a✝ = 3
⊢ a✝ = 4
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : ⦃ fun _ => True ⦄ three ⦃ fun r _ => r = 4 ⦄ := by
  vcgen
  trace_state
  all_goals sorry

/--
trace: case vc1
s✝¹ a✝¹ s✝ : Nat
a✝ : a✝¹ = 3
⊢ False
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : ⦃ fun _ => True ⦄ threeEq ⦃ fun r _ => r = 4 ⦄ := by
  vcgen
  trace_state
  all_goals sorry
