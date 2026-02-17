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
Same benchmark as `vcgen_add_sub_cancel` but using a deep transformer stack.
-/

abbrev M := ExceptT String <| ReaderT String <| ExceptT Nat <| StateT Nat <| ExceptT Unit <| StateM Unit

/-
Known issues:
* Using `StateT String` instead of `ReaderT String` picks the wrong spec for `MonadStateOf.get`; namely that on `String`.
  It seems we need to disambiguate discrimination tree lookup results with defeq.
* Even using `ReaderT String` it doesn't work. TODO: Why?
* But just using `ExceptT String` works.
-/

def step (v : Nat) : M Unit := do
  let s ← getThe Nat
  set (s + v)
  let s ← getThe Nat
  set (s - v)

def loop (n : Nat) : M Unit := do
  match n with
  | 0 => pure ()
  | n+1 => step n; loop n

def Goal (n : Nat) : Prop := ∀ post, ⦃post⦄ loop n ⦃⇓_ => post⦄

@[spec high]
theorem Spec.M_getThe_Nat :
    ⦃fun s₁ s₂ => Q.fst s₂ s₁ s₂⦄ getThe (m := M) Nat ⦃Q⦄ := by
  mvcgen

@[spec high]
theorem Spec.M_set_Nat (n : Nat) :
    ⦃fun s₁ _ => Q.fst ⟨⟩ s₁ n⦄ set (m := M) n ⦃Q⦄ := by
  mvcgen

set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

/-
example : Goal 20 := by
  simp only [Goal, loop, step]
  mvcgen' <;> grind
-/

#eval runBenchUsingTactic ``Goal [``loop, ``step] `(tactic| mvcgen' <;> sorry)
  [100, 200, 300, 400, 500, 600, 700, 800, 900, 1000]
  -- [1000]
