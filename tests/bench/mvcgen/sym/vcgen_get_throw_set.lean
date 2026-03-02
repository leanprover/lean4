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

abbrev M := ExceptT String <| StateM Nat

-- We partially evaluate a couple of specs for best performance.
-- If you comment those out, you will see a 4x slowdown.

@[spec high]
theorem Spec.throw_M {e : String} :
    ⦃Q.2.1 e⦄ throw (m := M) e ⦃Q⦄ := by
  mvcgen

@[spec high]
theorem Spec.set_M {s : Nat} :
    ⦃fun _ => Q.1 ⟨⟩ s⦄ set (m := M) s ⦃Q⦄ := by
  mvcgen

@[spec high]
theorem Spec.get_M :
    ⦃fun s => Q.1 s s⦄ get (m := M) ⦃Q⦄ := by
  mvcgen

def step (lim : Nat) : M Unit := do
  let s ← get
  if s > lim then
    throw "s is too large"
  set (s + 1)

def loop (n : Nat) : M Unit := do
  match n with
  | 0 => pure ()
  | n+1 => loop n; step n

def Goal (n : Nat) : Prop := ⦃fun s => ⌜s = 0⌝⦄ loop n ⦃⇓_ s => ⌜s = n⌝⦄

set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

#eval runBenchUsingTactic ``Goal [``loop, ``step] `(tactic| mvcgen') `(tactic| sorry)
  [100, 500, 1000]
  -- [1000]
