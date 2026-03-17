import Lean
open Lean Meta
opaque f : Nat → Nat

namespace SimpBench

/-!
## `MetaM` Simplifier benchmarks
-/

def mkSimpContext (config : Simp.Config := {}) : MetaM Simp.Context := do
  let s : SimpTheorems := {}
  let s ← s.addConst ``Nat.zero_add
  let config := { config with implicitDefEqProofs := false }
  Simp.mkContext config #[s] {}

def simp (e : Expr) : MetaM (Simp.Result × Float) := Sym.SymM.run' do
  -- let e ← Grind.shareCommon e
  let startTime ← IO.monoNanosNow
  let (r, _) ← Meta.simp e (← mkSimpContext)
  let endTime ← IO.monoNanosNow
  -- logInfo e
  -- logInfo r.expr
  -- check (← r.getProof)
  let timeMs := (endTime - startTime).toFloat / 1000000.0
  return (r, timeMs)

def mkTransitivityChain (n : Nat) : MetaM Expr := do
  withLocalDeclD `x (mkConst ``Nat) fun x => do
    let zero := mkNatLit 0
    let mut e := x
    for _ in [:n] do
      e := mkApp (mkConst ``f) (mkNatAdd zero e)
    mkForallFVars #[x] e

/-- Benchmark: transitivity chain construction -/
def benchTransChain (n : Nat) : MetaM Unit := do
  let e ← mkTransitivityChain n
  forallTelescope e fun _ e => do
    let (r, timeMs) ← simp e
    let proofSize ← r.proof?.get!.numObjs
    IO.println s!"trans_chain_{n}: {timeMs}ms, proof_size={proofSize}"

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

def benchCongrArgExplosion (depth width : Nat) : MetaM Unit := do
  let e ← mkCongrArgStress depth width
  forallTelescope e fun _ e => do
    let (r, timeMs) ← simp e
    let proofSize ← r.proof?.get!.numObjs
    IO.println s!"congr_arg_explosion_{depth}x{width}: {timeMs}ms, proof_size={proofSize}"

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
def benchManyRewrites (n : Nat) : MetaM Unit := do
  let e ← mkManySubterms n
  let (r, timeMs) ← simp e
  let proofSize ← r.proof?.get!.numObjs
  IO.println s!"many_rewrites_{n}: {timeMs}ms, proof_size={proofSize}"

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/-! ## Run all benchmarks -/
def runAllBenchmarks : MetaM Unit := do
  IO.println "=== Simplifier Stress Tests ==="
  IO.println ""

  IO.println ""
  IO.println "--- Benchmark 1: Transitivity chain ---"
  for n in [5, 50, 100, 200, 300, 400, 500, 600, 700, 800, 900, 1000, 2000, 3000, 4000, 5000] do
    benchTransChain n

  IO.println ""
  IO.println "--- Benchmark 2: CongrArg explosion ---"
  for n in [10, 20, 50, 100, 200, 300, 400, 500, 600, 700, 800, 900, 1000, 2000, 3000, 4000, 5000] do
    for w in [3] do
      benchCongrArgExplosion n w

  IO.println ""
  IO.println "--- Benchmark 3: Many rewrites ---"
  for n in [10, 50, 100, 200, 300, 400, 500, 600, 700, 800, 900, 1000, 2000, 3000, 4000, 5000] do
    benchManyRewrites n

#eval runAllBenchmarks

end SimpBench
