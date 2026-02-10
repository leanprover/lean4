import SymDirectly
import Lean

open Lean Meta Sym

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

def solveUsingSym (n : Nat) (check := true) : MetaM Unit := do
  driver n check fun mvarId => SymM.run do solve mvarId

def runBenchUsingSym : MetaM Unit := do
  IO.println "=== Symbolic Simulation Tests ==="
  IO.println ""
  for n in [100, 200, 300, 400, 500, 600, 700, 800, 900, 1000] do
    solveUsingSym n

set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

-- #eval runBenchUsingSym
#eval solveUsingSym 1000
