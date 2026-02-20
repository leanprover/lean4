import Lean
open Lean

abbrev Nat.Prime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ (m : Nat), m < p → 2 ≤ m → ¬m ∣ p

abbrev IsPrimePow (n : Nat) : Prop :=
  ∃ p ≤ n, ∃ k ≤ n, Nat.Prime p ∧ 0 < k ∧ p ^ k = n

def mkProblemInst (n : Nat) : Expr :=
  let n := mkNatLit n
  let f := mkApp (mkConst ``IsPrimePow) n
  mkApp (mkConst ``Not) f

def runSingleTest (n : Nat) : MetaM Unit := do
  let toFeed := mkProblemInst n
  let startTime ← IO.monoNanosNow
  let mvar ← Meta.mkFreshExprMVar toFeed
  let mvar := mvar.mvarId!
  let [mvar] ← mvar.applyConst ``of_decide_eq_true | throwError "Could not apply `of_decide_eq_true`"
  let executed ← Lean.Meta.Tactic.Cbv.cbvGoal mvar
  if (executed.isSome) then
    throwError "Did not fully reduce"
  let endTime ← IO.monoNanosNow
  let ms := (endTime - startTime).toFloat / 1000000.0
  let executed ← instantiateMVars (.mvar mvar)
  let startTime ← IO.monoNanosNow
  Meta.checkWithKernel executed
  let endTime ← IO.monoNanosNow
  let kernelMs := (endTime - startTime).toFloat / 1000000.0
  IO.println s!"cbv: goal_{n}: {ms} ms, kernel: {kernelMs} ms"

set_option maxHeartbeats 400000

def runCbvTests : MetaM Unit := do
  IO.println "=== Call-By-Value Tactic Tests ==="
  IO.println ""
  for n in [6,10,12,14,15,18,20] do
    runSingleTest n

#eval runCbvTests
