import Lean
open Lean Meta
opaque f : Nat → Nat

namespace SimpBench
/-!
## `SymM` Simplifier benchmarks
-/

def getProofSize (r : Sym.Simp.Result) : MetaM Nat := do
  match r with
  | .rfl _ => return 0
  | .step _ p _ => (ShareCommon.shareCommon' p).numObjs

def mkSimpMethods : MetaM Sym.Simp.Methods := do
  let thms : Sym.Simp.Theorems := {}
  let thms := thms.insert (← Sym.Simp.mkTheoremFromDecl ``Nat.zero_add)
  let thms := thms.insert (← Sym.Simp.mkTheoremFromDecl ``Nat.add_zero)
  return { post := thms.rewrite }

def simp (e : Expr) : MetaM (Sym.Simp.Result × Float) := Sym.SymM.run do
  let e ← Grind.shareCommon e
  let methods ← mkSimpMethods
  let startTime ← IO.monoNanosNow
  let r ← Sym.simp e methods { maxSteps := 100000000 }
  let endTime ← IO.monoNanosNow
  -- logInfo e
  -- match r with
  -- | .rfl _ => logInfo "rfl"
  -- | .step e' h _ => logInfo e'; logInfo h; check h
  let timeMs := (endTime - startTime).toFloat / 1000000.0
  return (r, timeMs)

def mkLetBench (n : Nat) (includeUnused : Bool) : MetaM Expr := do
  let zero := mkNatLit 0
  let one := mkNatLit 1
  let rec go (n : Nat) (xs : Array Expr) (v : Expr) (e : Expr) : MetaM Expr := do
    match n with
    | 0 => mkLetFVars (usedLetOnly := false) (generalizeNondepLet := false) xs e
    | n+1 =>
      if includeUnused && n % 2 == 0 then
        withLetDecl (nondep := true) `x (mkConst ``Nat) (mkNatAdd zero (mkNatAdd v one)) fun x =>
          go n (xs.push x) x (mkNatAdd zero (mkNatAdd e x))
      else
        withLetDecl (nondep := true) `y (mkConst ``Nat) zero fun y =>
          go n (xs.push y) v (mkNatAdd zero (mkNatAdd e zero))
  go n #[] zero zero

def benchLet (n : Nat) (includeUnused : Bool) : MetaM Unit := do
  let e ← mkLetBench n includeUnused
  let (r, timeMs) ← simp e
  let proofSize ← getProofSize r
  IO.println s!"have_{n}: {timeMs}ms, proof_size={proofSize}"

set_option maxRecDepth 100000

/-! ## Run all benchmarks -/
def runAllBenchmarks : MetaM Unit := do
  IO.println "=== Simplifier Stress Tests ==="
  IO.println ""

  IO.println ""
  IO.println "--- Benchmark 1: have block without unused variables ---"
  for n in [10, 20, 30, 40, 50, 60, 70, 80, 90, 100, 110, 120, 130, 140, 150, 200, 300, 400, 500,
    600, 700, 800, 900, 1000, 1200, 1400, 1600, 1800, 2000] do
    benchLet n false

  IO.println "--- Benchmark 2: have block with unused variables ---"
  for n in [10, 20, 30, 40, 50, 60, 70, 80, 90, 100, 110, 120, 130, 140, 150, 200, 300, 400, 500,
    600, 700, 800, 900, 1000, 1200, 1400, 1600, 1800, 2000] do
    benchLet n true

#eval runAllBenchmarks

end SimpBench
