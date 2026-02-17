/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import Lean
import VCGen
import Driver

open Lean Parser Meta Elab Tactic Sym Std Do SpecAttr

-- The following spec is necessary because the VC gen currently has no support for unfolding spec
-- theorems, which is what we usually do for `MonadState.get`.
@[spec]
theorem Spec.MonadState_get {m ps} [Monad m] [WPMonad m ps] {σ} {Q : PostCond σ (.arg σ ps)} :
    ⦃fun s => Q.fst s s⦄ get (m := StateT σ m) ⦃Q⦄ := by
  simp only [Triple, WP.get_MonadState, WP.get_StateT, SPred.entails.refl]

/-!
Same benchmark as `shallow_add_sub_cancel` but using `mvcgen`.
-/

def step (v : Nat) : StateM Nat Unit := do
  let s ← get
  set (s + v)
  let s ← get
  set (s - v)

def loop (n : Nat) : StateM Nat Unit := do
  match n with
  | 0 => pure ()
  | n+1 => step n; loop n

def Goal (n : Nat) : Prop := ∀ post, ⦃post⦄ loop n ⦃⇓_ => post⦄

set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

#eval runBenchUsingTactic ``Goal [``loop, ``step] `(tactic| mvcgen' <;> sorry)
  [100, 200, 300, 400, 500, 600, 700, 800, 900, 1000]
  -- [1000]
