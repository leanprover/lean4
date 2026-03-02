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
A variant of the `vcgen_add_sub_cancel` benchmark, but reading the value to subtract from `ReaderT`.
-/

abbrev M := ReaderT Nat <| StateM Nat

-- Partially evaluated specs for best performance.

@[spec high]
theorem Spec.M_read :
    ⦃fun r s => Q.fst r r s⦄ read (m := M) ⦃Q⦄ := by
  mvcgen

@[spec high]
theorem Spec.M_get :
    ⦃fun r s => Q.fst s r s⦄ get (m := M) ⦃Q⦄ := by
  mvcgen

@[spec high]
theorem Spec.M_set (n : Nat) :
    ⦃fun r _ => Q.fst () r n⦄ set (m := M) n ⦃Q⦄ := by
  mvcgen

def step : M Unit := do
  let r ← read
  let s ← get
  set (s + r)
  let s ← get
  set (s - r)

def loop (n : Nat) : M Unit := do
  match n with
  | 0 => pure ()
  | n+1 => step; loop n

def Goal (n : Nat) : Prop := ∀ post, ⦃post⦄ loop n ⦃⇓_ => post⦄

set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

#eval runBenchUsingTactic ``Goal [``loop, ``step] `(tactic| mvcgen') `(tactic| sorry) -- grind scales superlinearly here
  [100, 500, 1000]
  -- [1000]
