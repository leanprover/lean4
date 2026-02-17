/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module
public import Lean.Meta
import Lean.Elab

open Lean Parser Meta Elab Tactic Sym

/-- Helper function for executing a tactic `k` for solving `$(goal) n`. -/
def driver (goal : Name) (unfold : List Name) (n : Nat) (check := true) (k : MVarId → MetaM Unit) : MetaM Unit := do
  let mvar ← mkFreshExprMVar (mkApp (mkConst goal) (mkNatLit n))
-- The following code uses `Sym.simp`, but it balloons in the kernel. TODO: Investigate with new semantic
-- foundations. Use regular simp for now.
--  let mvarId ← SymM.run do
--    let mvarId ← preprocessMVar mvar.mvarId!
--    match (← Sym.simpGoal mvarId (← Sym.mkMethods "equational theorems of names in unfold as array")) with
--    | .goal mvarId => return mvarId
--    | .noProgress => throwError "SIMP NO PROGRESS on {mvarId}!"
--    | .closed => throwError "SIMP CLOSED!"
--  let unfold := Syntax.SepArray.ofElems (unfold.toArray |>.map (Lean.mkIdent ·))
  let lemmas ← unfold.toArray |>.push goal |>.mapM fun n => `(simpLemma| $(Lean.mkIdent n):term)
  let unfold := Syntax.TSepArray.ofElems (sep := ",") lemmas
  let ([mvarId], _) ← Lean.Elab.runTactic mvar.mvarId! (← `(tactic| simp only [$unfold,*])).raw {} {}
    | throwError "FAILED!"
  let startTime ← IO.monoNanosNow
  k mvarId
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

def solveUsingTactic (goal : Name) (unfold : List Name) (n : Nat) (solve : MetaM (TSyntax `tactic)) (check := true) : MetaM Unit := do
  driver goal unfold n check fun mvarId => do
    let ([], _) ← Lean.Elab.runTactic mvarId (← solve).raw {} {} | throwError "FAILED!"

/--
Solves a goal of the form `goal n` using the given tactic, where `n` ranges over `sizes`.
`unfold` is a list of `simp` lemmas to apply in order to unfold `goal n`.
For many benchmarks, this is `[step, loop]`.
-/
public def runBenchUsingTactic (goal : Name) (unfold : List Name) (solve : MetaM (TSyntax `tactic)) (sizes : List Nat) : MetaM Unit := do
  IO.println "=== VCGen tests ==="
  IO.println ""
  for n in sizes do
    solveUsingTactic goal unfold n solve

def solveUsingSym (goal : Name) (unfold : List Name) (n : Nat) (solve : MVarId → SymM Unit) (check := true) : MetaM Unit := do
  driver goal unfold n check fun mvarId => SymM.run do solve mvarId

/--
Solves a goal of the form `goal n` using a `SymM` procedure, where `n` ranges over `sizes`.
`unfold` is a list of `simp` lemmas to apply in order to unfold `goal n`.
For many benchmarks, this is `[step, loop]`.
-/
public def runBenchUsingSym (goal : Name) (unfold : List Name) (solve : MVarId → SymM Unit) (sizes : List Nat) : MetaM Unit := do
  IO.println "=== Symbolic Simulation Tests ==="
  IO.println ""
  for n in sizes do
    solveUsingSym goal unfold n solve
