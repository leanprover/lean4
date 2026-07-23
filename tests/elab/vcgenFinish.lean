/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import Std.Internal.Do
import Std.Tactic.Do

/-!
`vcgen … with finish` internalises each branch before solving it: a dead `match` branch leaves no
metavariable (`f_group_finish`), and a lifted precondition reaches grind's E-graph (`eat_spec_finish`).
-/

open Std.Internal.Do Lean.Order
set_option mvcgen.warning false
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
