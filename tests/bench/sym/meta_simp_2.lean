import Lean
open Lean Meta
opaque f : Nat → Nat

namespace SimpBench

/-!
## `MetaM` Simplifier benchmarks
-/
def getProofSize (r : Simp.Result) : MetaM Nat := do
  (← r.getProof).numObjs

def checkWithKernel (r : Simp.Result) : MetaM Float := do
  let p := ShareCommon.shareCommon' (← r.getProof)
  let startTime ← IO.monoNanosNow
  Meta.checkWithKernel p
  let endTime ← IO.monoNanosNow
  return (endTime - startTime).toFloat / 1000000.0

def mkSimpContext (config : Simp.Config := {}) : MetaM Simp.Context := do
  let s : SimpTheorems := {}
  let s ← s.addConst ``Nat.zero_add
  let s ← s.addConst ``Nat.add_zero
  let config := { config with implicitDefEqProofs := false }
  Simp.mkContext config #[s] {}

def simp (e : Expr) : MetaM (Simp.Result × Float) := do
  -- let e ← Grind.shareCommon e
  let startTime ← IO.monoNanosNow
  let (r, _) ← Meta.simp e (← mkSimpContext)
  let endTime ← IO.monoNanosNow
  -- logInfo e
  -- logInfo r.expr
  -- check (← r.getProof)
  let timeMs := (endTime - startTime).toFloat / 1000000.0
  return (r, timeMs)

def ppExample (e : Expr) (info := false) : MetaM Unit := do
  forallTelescope e fun _ e => do
  IO.println "Example:"
  IO.println (← ppExpr e)
  IO.println "====>"
  let (r, _) ← simp e
  IO.println (← ppExpr r.expr)
  let h ← r.getProof
  IO.println "Proof:"
  if info then
    logInfo h
  else
    IO.println (← ppExpr h)

def mkLambdaBench (n : Nat) : MetaM Expr := do
  let zero := mkNatLit 0
  let one := mkNatLit 1
  let rec go (n : Nat) (xs : Array Expr) (e : Expr) : MetaM Expr := do
    match n with
    | 0 => mkLambdaFVars xs e
    | n+1 =>
      withLocalDeclD `x (mkConst ``Nat) fun x =>
        go n (xs.push x) (mkNatAdd zero (mkNatAdd e (mkNatAdd (mkNatAdd x one) zero)))
  go n #[] zero

def benchLambda (n : Nat) (check := false) : MetaM Unit := do
  let e ← mkLambdaBench n
  let (r, timeMs) ← simp e
  let proofSize ← getProofSize r
  if check then
    let kMs ← checkWithKernel r
    IO.println s!"lambda_{n}: {timeMs}ms, kernel: {kMs}ms, proof_size={proofSize}"
  else
    IO.println s!"lambda_{n}: {timeMs}ms, proof_size={proofSize}"

set_option maxRecDepth 100000

/-! ## Run all benchmarks -/
def runAllBenchmarks : MetaM Unit := do
  IO.println "=== Simplifier Lambda Telescope Stress Tests using `Meta.simp` ==="
  IO.println ""

  IO.println ""
  IO.println "--- Benchmark 1: Lambda Telescope block ---"
  ppExample (← mkLambdaBench 5)
  for n in [10, 20, 30, 40, 50, 60, 70, 80, 90, 100, 110, 120, 130, 140, 150, 160, 170, 180, 190, 200] do
    benchLambda n (n < 500)

#eval runAllBenchmarks

end SimpBench
