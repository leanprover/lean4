/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import Lean
import VCGen

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

/-- Helper function for executing a tactic `k` for solving `Goal n`. -/
def driver (n : Nat) (check := true) (k : MVarId → MetaM Unit) : MetaM Unit := do
  let some goal ← unfoldDefinition? (mkApp (mkConst ``Goal) (mkNatLit n)) | throwError "UNFOLD FAILED!"
  let mvar ← mkFreshExprMVar goal
  let startTime ← IO.monoNanosNow
  k mvar.mvarId!
  let endTime ← IO.monoNanosNow
  let ms := (endTime - startTime).toFloat / 1000000.0
  if check then
    let startTime ← IO.monoNanosNow
    checkWithKernel (← instantiateExprMVars mvar)
    let endTime ← IO.monoNanosNow
    let kernelMs := (endTime - startTime).toFloat / 1000000.0
    IO.println s!"goal_{n}: {ms} ms, kernel: {kernelMs} ms"
  else
    IO.println s!"goal_{n}: {ms} ms"

/-
A tactic for solving goal `Goal n`
-/
macro "solve" : tactic => `(tactic| {
  simp only [loop, step]
  mvcgen'
  all_goals sorry
  -- all_goals grind
})

/--
Solves a goal of the form `Goal n` using the `solve` tactic.
-/
def solveUsingMeta (n : Nat) (check := true) : MetaM Unit := do
  driver n check fun mvarId => do
    let ([], _) ← Lean.Elab.runTactic mvarId (← `(tactic| solve)).raw {} {} | throwError "FAILED!"

def runBenchUsingMeta (sizes : List Nat) : MetaM Unit := do
  IO.println "=== VCGen tests ==="
  IO.println ""
  for n in sizes do
    solveUsingMeta n

set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

/-
example : Goal 20 := by
  simp only [Goal, loop, step]
  mvcgen'
  all_goals sorry
-/

#eval runBenchUsingMeta [100, 200, 300, 400, 500, 600, 700, 800, 900, 1000]
-- #eval runBenchUsingMeta [1000]
