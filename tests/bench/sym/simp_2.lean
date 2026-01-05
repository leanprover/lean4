import Lean
open Lean Meta
opaque f : Nat → Nat

namespace SimpBench
/-!
## `SymM` Simplifier benchmarks
-/

def getProofSize (r : Sym.Simp.Result) : MetaM Nat :=
  match r with
  | .rfl _ => return 0
  | .step _ p _ => p.numObjs

def mkSimpMethods : MetaM Sym.Simp.Methods := do
  let thms : Sym.Simp.Theorems := {}
  let thm ← Sym.Simp.mkTheoremFromDecl ``Nat.zero_add
  let thms := thms.insert thm
  return { post := thms.rewrite }

def simp (e : Expr) : MetaM (Sym.Simp.Result × Float) := Sym.SymM.run' do
  let e ← Grind.shareCommon e
  let methods ← mkSimpMethods
  let startTime ← IO.monoNanosNow
  let r ← Sym.simp e methods { maxSteps := 100000000 }
  let endTime ← IO.monoNanosNow
  -- logInfo e
  -- match r with
  -- | .rfl => logInfo "rfl"
  -- | .step e' h => logInfo e'; logInfo h; check h
  let timeMs := (endTime - startTime).toFloat / 1000000.0
  return (r, timeMs)

def mkLambdaBench (n : Nat) : MetaM Expr := do
  let zero := mkNatLit 0
  let rec go (n : Nat) (xs : Array Expr) (e : Expr) : MetaM Expr := do
    match n with
    | 0 => mkLambdaFVars xs e
    | n+1 =>
      withLocalDeclD `x (mkConst ``Nat) fun x =>
        go n (xs.push x) (mkNatAdd zero (mkNatAdd e x))
  go n #[] zero

def benchLambda (n : Nat) : MetaM Unit := do
  let e ← mkLambdaBench n
  let (r, timeMs) ← simp e
  let proofSize ← getProofSize r
  IO.println s!"lambda_{n}: {timeMs}ms, proof_size={proofSize}"

set_option maxRecDepth 100000

/-! ## Run all benchmarks -/
def runAllBenchmarks : MetaM Unit := do
  IO.println "=== Simplifier Stress Tests ==="
  IO.println ""

  IO.println ""
  IO.println "--- Benchmark 1: Lambda block ---"
  for n in [10, 20, 30, 40, 50, 60, 70, 80, 90, 100, 110, 120, 130, 140, 150, 160, 170, 180, 190, 200] do
    benchLambda n

#eval runAllBenchmarks

end SimpBench
