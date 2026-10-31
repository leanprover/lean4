import Lean

/-!
# Benchmark for the `arith` simproc of `Sym.simp`

Closes `t = t'` goals where `t` and `t'` are equal polynomials written with different
shapes, measuring `Sym.simp` with `simpArith` and the kernel check of the produced proof.
Problem sizes are scaled by `TEST_BENCH`.
-/

open Lean Meta Sym

/-- `x₀ + x₁ + ... + xₙ₋₁` over fresh atoms (left-nested), and the reversed sum. -/
def mkSum (xs : Array Expr) (rev : Bool) : Expr :=
  let xs := if rev then xs.reverse else xs
  xs[1:].foldl (init := xs[0]!) fun acc x => mkIntAdd acc x

/-- `(x₀ + 1) ^ k` and `(1 + x₀) ^ k`. -/
def mkPow (x : Expr) (k : Nat) (rev : Bool) : Expr :=
  let base := if rev then mkIntAdd (mkIntLit 1) x else mkIntAdd x (mkIntLit 1)
  mkApp6 (mkConst ``HPow.hPow [0, 0, 0]) Int.mkType Nat.mkType Int.mkType Int.mkInstHPow base (mkNatLit k)

def runCase (name : String) (mk : Array Expr → Bool → Expr) (numAtoms : Nat) : MetaM Unit := do
  let decls := (Array.range numAtoms).map fun i => (Name.mkSimple s!"x{i}", fun _ => pure Int.mkType)
  withLocalDeclsD decls fun xs => do
    let goal ← mkFreshExprMVar (← mkEq (mk xs false) (mk xs true))
    let start ← IO.monoNanosNow
    let closed ← SymM.run do
      let mvarId ← preprocessMVar goal.mvarId!
      let methods : Sym.Simp.Methods := { pre := Sym.Simp.simpArith, post := Sym.Simp.evalGround }
      return (← simpGoal mvarId methods) matches SimpGoalResult.closed
    let simpMs := (← IO.monoNanosNow) - start
    unless closed do throwError "{name}: goal not closed"
    let start ← IO.monoNanosNow
    let proof ← instantiateMVars goal
    let proof ← mkLambdaFVars xs proof
    Meta.checkWithKernel proof
    let kernelNs := (← IO.monoNanosNow) - start
    IO.println s!"{name}: simp {simpMs / 1000} µs, kernel {kernelNs / 1000} µs, proof size {proof.sizeWithoutSharing}"

def runAll : MetaM Unit := do
  let bench := (← IO.getEnv "TEST_BENCH") == some "1"
  let sumSizes := if bench then [50, 100, 200] else [20]
  let powSizes := if bench then [10, 20, 40] else [6]
  for n in sumSizes do
    runCase s!"sum_{n}" mkSum n
  for k in powSizes do
    runCase s!"pow_{k}" (fun xs rev => mkPow xs[0]! k rev) 1

set_option sym.arith.maxTerms 1000 in
set_option sym.arith.maxDegree 1000 in
#eval runAll
