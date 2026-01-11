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

def checkWithKernel (r : Sym.Simp.Result) : MetaM Float := do
  match r with
  | .rfl _ => return 0.0
  | .step _ p _ =>
    let p := ShareCommon.shareCommon' p
    let startTime ← IO.monoNanosNow
    Meta.checkWithKernel p
    let endTime ← IO.monoNanosNow
    return (endTime - startTime).toFloat / 1000000.0

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
  let timeMs := (endTime - startTime).toFloat / 1000000.0
  -- logInfo e
  -- match r with
  -- | .rfl _ => logInfo "rfl"
  -- | .step e' h _ =>
  --   logInfo e'; logInfo h
  return (r, timeMs)

def ppExample (e : Expr) : MetaM Unit := do
  forallTelescope e fun _ e => do
  IO.println "Example:"
  IO.println (← ppExpr e)
  IO.println "====>"
  match (← simp e).1 with
  | .rfl _ => IO.println "<no change>"
  | .step e' h _ =>
    IO.println (← ppExpr e')
    IO.println (← ppExpr h)
  IO.println ""

def benchSimp (name : String) (e : Expr) (check := false) : MetaM Unit :=
  forallTelescope e fun _ e => do
  let (r, timeMs) ← simp e
  let proofSize ← getProofSize r
  if check then
    let kMs ← checkWithKernel r
    IO.println s!"{name}: {timeMs}ms, kernel: {kMs}ms, proof_size={proofSize}"
  else
    IO.println s!"{name}: {timeMs}ms, proof_size={proofSize}"

def mkHaveChainBench (n : Nat) (includeUnused : Bool) : MetaM Expr := do
  let zero := mkNatLit 0
  let one := mkNatLit 1
  let rec go (n : Nat) (xs : Array Expr) (v : Expr) (e : Expr) : MetaM Expr := do
    match n with
    | 0 => mkLetFVars (usedLetOnly := false) (generalizeNondepLet := false) xs e
    | n+1 =>
      if !includeUnused || n % 2 == 0 then
        withLetDecl (nondep := true) `x (mkConst ``Nat) (mkNatAdd zero (mkNatAdd v one)) fun x =>
          go n (xs.push x) x (mkNatAdd zero (mkNatAdd e x))
      else
        withLetDecl (nondep := true) `y (mkConst ``Nat) zero fun y =>
          go n (xs.push y) v (mkNatAdd zero (mkNatAdd e zero))
  go n #[] zero zero

def benchHaveChain (n : Nat) (includeUnused : Bool) (check : Bool := false) : MetaM Unit := do
  let e ← mkHaveChainBench n includeUnused
  let name := if includeUnused then s!"have_chain_unused_{n}" else s!"have_chain_{n}"
  benchSimp name e check

def mkHaveParallelBench (n : Nat) (simpValues : Bool) : MetaM Expr := do
  withLocalDeclD `x Nat.mkType fun x => do
    let zero := mkNatLit 0
    let rec go (n : Nat) (xs : Array Expr) (e : Expr) : MetaM Expr := do
      match n with
      | 0 => mkLetFVars (usedLetOnly := false) (generalizeNondepLet := false) xs e
      | n+1 =>
        let val := if simpValues then
          -- Values should be in `simp` normal form
          mkNatAdd x (mkNatLit n)
        else
          mkNatAdd zero (mkNatAdd x (mkNatLit n))
        withLetDecl (nondep := true) `y (mkConst ``Nat) val fun x =>
          go n (xs.push x) (mkNatAdd x e)
    let r ← go n #[] zero
    mkForallFVars #[x] r

def benchHaveParallel (n : Nat) (simpValues : Bool) (check : Bool := false) : MetaM Unit := do
  let e ← mkHaveParallelBench n simpValues
  let name := if simpValues then s!"have_parallel_simp_vals_{n}" else s!"have_parallel_unsimp_vals_{n}"
  benchSimp name e check

def mkHaveChain1Bench (n : Nat) : MetaM Expr := do
  let zero := mkNatLit 0
  let one := mkNatLit 1
  let rec go (n : Nat) (xs : Array Expr) (v : Expr) (e : Expr) : MetaM Expr := do
    match n with
    | 0 => mkLetFVars (usedLetOnly := false) (generalizeNondepLet := false) xs (mkNatAdd v e)
    | n+1 =>
      withLetDecl (nondep := true) `x (mkConst ``Nat) (mkNatAdd zero (mkNatAdd v one)) fun x =>
        go n (xs.push x) x (mkNatAdd one e)
  go n #[] zero zero

def benchHaveChain1 (n : Nat) (check : Bool := false) : MetaM Unit := do
  let e ← mkHaveChain1Bench n
  benchSimp s!"have_chain1_{n}" e check

def run (k : Nat → MetaM Unit) : MetaM Unit := do
  for n in [10, 20, 30, 40, 50, 60, 70, 80, 90, 100, 110, 120, 130, 140, 150, 200, 300, 400, 500] do
    k n

set_option maxRecDepth 100000

/-! ## Run all benchmarks -/
def runAllBenchmarks : MetaM Unit := do
  IO.println "=== Simplifier Have-telescope Stress Tests ==="
  IO.println ""

  IO.println ""
  IO.println "--- Benchmark 1: have-telescope chain without unused variables ---"
  ppExample (← mkHaveChainBench 5 false)
  run fun n => benchHaveChain n false true

  IO.println "--- Benchmark 2: have-telescope chain with unused variables ---"
  ppExample (← mkHaveChainBench 5 true)
  run fun n => benchHaveChain n true true

  IO.println "--- Benchmark 3: have-telescope parallel declarations with simplified values ---"
  ppExample (← mkHaveParallelBench 5 true)
  run fun n => benchHaveParallel n true true

  IO.println "--- Benchmark 4: have-telescope parallel declarations with unsimplified values ---"
  ppExample (← mkHaveParallelBench 5 false)
  run fun n => benchHaveParallel n false true

  IO.println ""
  IO.println "--- Benchmark 5: have-telescope chain with 1 dep ---"
  ppExample (← mkHaveChain1Bench 5)
  run fun n => benchHaveChain1 n true

#eval runAllBenchmarks

end SimpBench
