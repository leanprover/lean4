import Lean

/-!
Synthesize `Decidable (True → q)` given `Decidable q`, where `q` is built by
repeatedly sharing `q ∧ q`. The generic forall instance introduces an unused
proof argument. Removing that argument must visit the shared expression as a
DAG, rather than expanding its exponentially large tree.
-/

open Lean Meta

run_meta do
  let bench := (← IO.getEnv "TEST_BENCH") == some "1"
  withLocalDeclD `p (mkSort .zero) fun p => do
    for depth in (if bench then [16, 20, 24, 28] else [8]) do
      let q := (List.range depth).foldl (fun q _ => mkApp2 (mkConst ``And) q q) p
      withLocalDecl `inst .instImplicit (mkApp (mkConst ``Decidable) q) fun inst => do
        let target := mkApp (mkConst ``Decidable) (← mkArrow (mkConst ``True) q)
        let start ← IO.monoNanosNow
        let result ← synthInstance target
        let elapsed := (← IO.monoNanosNow) - start
        checkWithKernel (← mkLambdaFVars #[p, inst] result)
        if bench then
          IO.println s!"measurement: synth_depth_{depth} {elapsed} ns"
