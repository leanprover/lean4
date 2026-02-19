/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module
public import Lean.Meta
import Lean.Elab
import Lean.Meta.Sym.Simp.Theorems

open Lean Parser Meta Elab Tactic Sym

def timeItMs (k : MetaM α) : MetaM (α × UInt64) := do
  let startTime ← IO.monoNanosNow
  let a ← k
  let endTime ← IO.monoNanosNow
  let ms := (endTime - startTime).toFloat / 1000000.0
  return (a, ms.toUInt64)

/-- Helper function for executing a tactic `k` for solving `$(goal) n`. -/
def driver (goal : Name) (unfold : List Name) (n : Nat) (discharge : MetaM (TSyntax `tactic)) (k : MVarId → MetaM (List MVarId)) : MetaM Unit := do
  let mvar ← mkFreshExprMVar (mkApp (mkConst goal) (mkNatLit n))
  let (mvarId, _unfoldMs) ← timeItMs do SymM.run do
    let mvarId ← preprocessMVar mvar.mvarId!
    let eqnss ← unfold.toArray
      |>.push goal
      |>.mapM fun n => getEqnsFor? n
    let thms := eqnss.flatMap (fun o => o.getD #[])
    match (← Sym.simpGoal mvarId (← Sym.mkMethods thms)) with
    | .goal mvarId => return mvarId
    | .noProgress => throwError "No progress when simping {mvarId}!"
    | .closed => throwError "Simp closed goal {mvarId}"
  -- IO.println s!"time spent unfolding: {_unfoldMs} ms"
  let (mvarIds, ms) ← timeItMs do k mvarId
  let discharge ← discharge
  let dischargePp ← PrettyPrinter.ppTactic discharge
  let dischargeMs? ← OptionT.run <| do
    guard !mvarIds.isEmpty
    Prod.snd <$> timeItMs do
      for mvarId in mvarIds do
        let ([], _) ← Lean.Elab.runTactic mvarId discharge.raw {} {}
          | throwError "{dischargePp} failed to solve {mvarId}"
  let (expr, instMs) ← timeItMs (instantiateMVars mvar)
  -- Emulate the shareCommonPreDefs step before sending the term to the kernel.
  -- If we don't do this, kernel checking time balloons.
  let expr ← SymM.run (shareCommon expr)
  let (_, kernelMs) ← timeItMs (checkWithKernel expr)
  let mut msg := s!"goal_{n}: {ms} ms"
  if let some dischargeMs := dischargeMs? then
    msg := msg ++ s!", {mvarIds.length} VCs by {dischargePp}: {dischargeMs} ms"
  else
    msg := msg ++ s!", {mvarIds.length} VCs"
  if instMs > 1000 then
    msg := msg ++ s!", instantiate > 1000ms: {instMs} ms"
  msg := msg ++ s!", kernel: {kernelMs} ms"
  IO.println msg

def solveUsingTactic (goal : Name) (unfold : List Name) (n : Nat) (solve : MetaM (TSyntax `tactic)) (discharge : MetaM (TSyntax `tactic)) : MetaM Unit := do
  driver goal unfold n discharge fun mvarId => do
    let (mvarIds, _) ← Lean.Elab.runTactic mvarId (← solve).raw {} {}
    return mvarIds

/--
Solves a goal of the form `goal n` using the given tactic, where `n` ranges over `sizes`.
`unfold` is a list of `simp` lemmas to apply in order to unfold `goal n`.
For many benchmarks, this is `[step, loop]`.
-/
public def runBenchUsingTactic (goal : Name) (unfold : List Name) (solve : MetaM (TSyntax `tactic)) (discharge : MetaM (TSyntax `tactic)) (sizes : List Nat) : MetaM Unit := do
  for n in sizes do
    solveUsingTactic goal unfold n solve discharge

def solveUsingSym (goal : Name) (unfold : List Name) (n : Nat) (solve : MVarId → SymM (List MVarId)) (discharge : MetaM (TSyntax `tactic)) : MetaM Unit := do
  driver goal unfold n discharge fun mvarId => SymM.run do solve mvarId

/--
Solves a goal of the form `goal n` using a `SymM` procedure, where `n` ranges over `sizes`.
`unfold` is a list of `simp` lemmas to apply in order to unfold `goal n`.
For many benchmarks, this is `[step, loop]`.
-/
public def runBenchUsingSym (goal : Name) (unfold : List Name) (solve : MVarId → SymM (List MVarId)) (discharge : MetaM (TSyntax `tactic)) (sizes : List Nat) : MetaM Unit := do
  for n in sizes do
    solveUsingSym goal unfold n solve discharge
