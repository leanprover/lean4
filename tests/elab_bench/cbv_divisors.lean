import Lean
open Lean

def divisorsList (n : Nat) : List Nat :=
  (List.range' 1 n).filter fun d => n % d = 0

def mkProblem (n : Nat) : Expr := mkApp (mkConst ``divisorsList) (mkNatLit n)

def runProblem (n : Nat) : MetaM Unit := do
  let problem := mkProblem n
  let startTime ← IO.monoNanosNow
  let executed ← Lean.Meta.Tactic.Cbv.cbvEntry problem
  let endTime ← IO.monoNanosNow
  let ms := (endTime - startTime).toFloat / 1000000.0
  match executed with
  | .rfl _ => IO.println s!"goal_{n}: {ms} ms"
  | .step _ proof _ =>
    let startTime ← IO.monoNanosNow
    Meta.checkWithKernel proof
    let endTime ← IO.monoNanosNow
    let kernelMs := (endTime - startTime).toFloat / 1000000.0
    IO.println s!"cbv: goal_{n}: {ms} ms, kernel: {kernelMs} ms"

def runCbvTests : MetaM Unit := do
  IO.println "=== Call-By-Value Tactic Tests ==="
  IO.println ""
  for n in List.range 200 do
    runProblem n

#eval runCbvTests
