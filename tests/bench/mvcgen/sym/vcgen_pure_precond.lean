/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import Lean
import VCGen
import Driver

open Lean Parser Meta Elab Tactic Sym Std Do SpecAttr

set_option mvcgen.warning false

/-!
A benchmark where VCs carry pure hypotheses `⌜φ⌝` on the left of `⊢ₛ`.
The precondition `⌜s = 0⌝` propagates through VCGen, producing VCs
of the form `⌜s₀ = 0⌝ ⊢ₛ ⌜ψ⌝`. Discharging these VCs requires
moving the pure hypothesis into the Lean local context
(e.g., via `SPred.pure_mono` or `Frame.frame`).
-/

-- Partially evaluated specs for best performance.

def flipp (_ : Bool) : StateM Bool Unit := modify not

theorem Spec.flipp_false :
    ⦃fun b => ⌜b = false⌝⦄ flipp false ⦃⇓ _ b => ⌜b = true⌝⦄ := by
  mvcgen [flipp] <;> grind

theorem Spec.flipp_true :
    ⦃fun b => ⌜b = true⌝⦄ flipp true ⦃⇓ _ b => ⌜b = false⌝⦄ := by
  mvcgen [flipp] <;> grind

attribute [spec] Spec.flipp_true Spec.flipp_false

def step : StateM Bool Unit := do
  flipp true
  flipp false

def loop (n : Nat) : StateM Bool Unit := do
  match n with
  | 0 => pure ()
  | n+1 => step; loop n

def Goal (n : Nat) : Prop := ⦃fun b => ⌜b = true⌝⦄ loop n ⦃⇓ _ b => ⌜b = true⌝⦄

set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

example : Goal 10 := by
  simp only [Goal, loop, step]
  mvcgen'

#eval runBenchUsingTactic ``Goal [``loop, ``step] `(tactic| mvcgen') `(tactic| fail)
  [100, 500, 1000]
