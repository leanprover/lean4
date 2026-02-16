/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import Lean
import VCGen
import Driver

open Lean Parser Meta Elab Tactic Sym Std Do SpecAttr

@[spec]
theorem Spec.monadLift_ExceptT [Monad m] [WPMonad m ps] {x : m α} :
    ⦃wp⟦x⟧ (Q.1, Q.2.2)⦄ monadLift (n := ExceptT ε m) x ⦃Q⦄ := by
  simp [Triple.iff, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, ExceptT.lift, wp]

def step (lim : Nat) : ExceptT String (StateM Nat) Unit := do
  let s ← get
  if s > lim then
    throw "s is too large"
  set (s + 1)

def loop (n : Nat) : ExceptT String (StateM Nat) Unit := do
  match n with
  | 0 => pure ()
  | n+1 => loop n; step n

def Goal (n : Nat) : Prop := ⦃fun s => ⌜s = 0⌝⦄ loop n ⦃⇓_ s => ⌜s = n⌝⦄

set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

/-
example : Goal 20 := by
  simp only [Goal, loop, step]
  mvcgen'
  all_goals sorry
-/

#eval runBenchUsingTactic ``Goal [``loop, ``step] `(tactic| mvcgen' <;> sorry)
  [100, 200, 300, 400, 500, 600, 700, 800, 900, 1000]
  -- [1000]
