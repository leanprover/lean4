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
  let thm ← Sym.Simp.mkTheoremFromDecl ``Nat.zero_add
  let thms := thms.insert thm
  return { post := thms.rewrite }

def simp (e : Expr) : MetaM (Sym.Simp.Result × Float) := Sym.SymM.run do
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

def benchSimp (name : String) (e : Expr) (check := false) : MetaM Unit :=
  forallTelescope e fun _ e => do
  let (r, timeMs) ← simp e
  let proofSize ← getProofSize r
  if check then
    let kMs ← checkWithKernel r
    IO.println s!"{name}: {timeMs}ms, kernel: {kMs}ms, proof_size={proofSize}"
  else
    IO.println s!"{name}: {timeMs}ms, proof_size={proofSize}"

def ppExample (e : Expr) (info := false) : MetaM Unit := do
  forallTelescope e fun _ e => do
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

def mkTransitivityChain (n : Nat) : MetaM Expr := do
  withLocalDeclD `x (mkConst ``Nat) fun x => do
    let zero := mkNatLit 0
    let mut e := x
    for _ in [:n] do
      e := mkApp (mkConst ``f) (mkNatAdd zero e)
    mkForallFVars #[x] e

/-- Benchmark: transitivity chain construction -/
def benchTransChain (n : Nat) (check := true) : MetaM Unit := do
  let e ← mkTransitivityChain n
  benchSimp s!"trans_chain_{n}" e check

def mkCongrArgStress (depth width : Nat) : MetaM Expr := do
  -- Create a term with `depth` layers of functions, each with `width` arguments
  -- The last argument at each level contains a simplifiable term
  let nat := mkConst ``Nat
  let mut fnType := nat
  for _ in [:width] do
    fnType := mkForall `x .default nat fnType

  withLocalDeclsD (List.range depth |>.toArray.map fun i =>
    (Name.mkSimple s!"f{i}", fun _ => pure fnType)) fun fs => do

    -- Innermost: a term that simplifies, e.g., 0 + 0
    let zero := mkNatLit 0
    let mut inner := mkNatAdd zero zero

    -- Wrap in depth layers of function applications
    -- Each layer: fᵢ dummy dummy ... dummy inner
    for f in fs.reverse do
      let mut app := f
      -- width-1 dummy arguments
      for _ in [:width - 1] do
        app := mkApp app zero
      -- last argument is the interesting one
      app := mkApp app inner
      inner := app

    mkForallFVars fs inner

def benchCongrArgExplosion (depth width : Nat) (check := true) : MetaM Unit := do
  let e ← mkCongrArgStress depth width
  benchSimp s!"congr_arg_explosion_{depth}x{width}" e check

-- We simulate this by having many structurally similar subterms
def mkManySubterms (n : Nat) : MetaM Expr := do
  -- Create: (0 + 1, (0 + 2, (0 + 3, ...)))
  -- Each `0 + k` matches the simp lemma pattern
  let zero := mkNatLit 0
  let mut e := zero
  for i in [:n] do
    let k := mkNatLit (i + 1)
    let term := mkNatAdd zero k
    e ← mkAppM ``Prod.mk #[term, e]
  return e

/-- Benchmark: many rewrite candidates -/
def benchManyRewrites (n : Nat) (check := true) : MetaM Unit := do
  let e ← mkManySubterms n
  benchSimp s!"many_rewrites_{n}" e check

def mkTermTree (n : Nat) : MetaM Expr := do
  withLocalDeclD `x Nat.mkType fun x => do
    mkForallFVars #[x] (← go x n 0)
where
  go (x : Expr) (n : Nat) (i : Nat) : MetaM Expr := do
    if h : n = 0 then
      return mkNatAdd (mkNatLit 0) (mkNatAdd (mkNatLit i) x)
    else
      let lhs ← go x (n/2) i
      let rhs ← go x (n/2) (i + n/2)
      mkAppM ``Prod.mk #[lhs, rhs]

def benchTermTree (n : Nat) (check := true) : MetaM Unit := do
  let e ← mkTermTree n
  benchSimp s!"term_tree_{n}" e check


def run (k : Nat → MetaM Unit) : MetaM Unit := do
  for n in [10, 20, 50, 100, 200, 300, 400, 500, 600, 700, 800, 900, 1000, 2000, 3000, 4000, 5000] do
    k n

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-! ## Run all benchmarks -/
def runAllBenchmarks : MetaM Unit := do
  IO.println "=== Simplifier Stress Tests ==="
  IO.println ""

  IO.println ""
  IO.println "--- Benchmark 1: Transitivity chain ---"
  ppExample (← mkTransitivityChain 5)
  run benchTransChain

  IO.println ""
  IO.println "--- Benchmark 2: CongrArg explosion ---"
  ppExample (← mkCongrArgStress 5 3)
  run (benchCongrArgExplosion · 3)

  IO.println ""
  IO.println "--- Benchmark 3: Many rewrites ---"
  ppExample (← mkManySubterms 5)
  run benchManyRewrites

  IO.println ""
  IO.println "--- Benchmark 4: Term tree rewrites ---"
  ppExample (← mkTermTree 8)
  run benchTermTree

#eval runAllBenchmarks

end SimpBench
