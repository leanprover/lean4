import Lean
open Lean Meta
opaque f : Nat → Nat

namespace SimpBench
/-!
## `SymM` Simplifier benchmarks
-/

def implies (p q : Prop) := p → q

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

def ppExample (e : Expr) (info := false) : MetaM Unit := do
  IO.println "Example:"
  IO.println (← ppExpr e)
  IO.println "====>"
  match (← simp e).1 with
  | .rfl _ => IO.println "<no change>"
  | .step e' h _ =>
    IO.println (← ppExpr e')
    IO.println "Proof:"
    if info then
      logInfo h
    else
      IO.println (← ppExpr h)
  IO.println ""

def benchSimp (name : String) (e : Expr) (check := false) : MetaM Unit := do
  let (r, timeMs) ← simp e
  let proofSize ← getProofSize r
  if check then
    let kMs ← checkWithKernel r
    IO.println s!"{name}: {timeMs}ms, kernel: {kMs}ms, proof_size={proofSize}"
  else
    IO.println s!"{name}: {timeMs}ms, proof_size={proofSize}"

def mkForallPrefix (n : Nat) (k : Array Expr → MetaM Expr) : MetaM Expr := do
  let rec go (n : Nat) (xs : Array Expr) : MetaM Expr := do
    match n with
    | 0 => mkForallFVars xs (← k xs)
    | n+1 =>
      withLocalDeclD `x (mkConst ``Nat) fun x =>
      go n (xs.push x)
  go n #[]

def mkForallBench (n : Nat) (useImplies : Bool) : MetaM Expr :=
  mkForallPrefix n fun xs => do
    let rec go (n : Nat) (e : Expr) : MetaM Expr := do
      match n with
      | 0 => return e
      | n+1 =>
        if useImplies then
          go n (mkApp2 (mkConst ``implies) (mkNatEq xs[n]! (mkNatAdd (mkNatLit 0) xs[n]!)) e)
        else
          go n (← mkArrow (mkNatEq xs[n]! (mkNatAdd (mkNatLit 0) xs[n]!)) e)
    go n (mkConst ``True)

def benchForall (n : Nat) (useImplies : Bool) (check := false) : MetaM Unit := do
  let e ← mkForallBench n useImplies
  benchSimp s!"forall_{n}" e check

set_option maxRecDepth 100000

/-! ## Run all benchmarks -/
def runAllBenchmarks : MetaM Unit := do
  IO.println "=== Simplifier Forall Telescope Stress Tests ==="
  IO.println ""

  IO.println ""
  IO.println "--- Benchmark 1: Forall Telescope block using arrows in the body ---"
  ppExample (← mkForallBench 5 false)

  for n in [10, 20, 30, 40, 50, 60, 70, 80, 90, 100, 110, 120, 130, 140, 150, 160, 170, 180, 190, 200, 300, 400] do
    benchForall n false (n < 500)

  IO.println ""
  IO.println "--- Benchmark 1: Forall Telescope block using `implies` in the body ---"
  ppExample (← mkForallBench 5 true)

  for n in [10, 20, 30, 40, 50, 60, 70, 80, 90, 100, 110, 120, 130, 140, 150, 160, 170, 180, 190, 200, 300, 400] do
    benchForall n true (n < 500)

#eval runAllBenchmarks

end SimpBench
