import Lean

/-!
This benchmark exercises `instantiateMVars` sharing on an exponential DAG
of delayed metavariable assignments.

We build a chain of n delayed mvars:
  ?d₀  delayed [x] := x
  ?dᵢ  delayed [x] := Nat.add (?dᵢ₋₁ x) (?dᵢ₋₁ x)
  ?root := fun (a : Nat) => ?dₙ a

Without sharing, instantiating ?root would produce 2ⁿ leaf nodes.
With sharing, it produces O(n) unique subexpressions.
-/

set_option maxHeartbeats 40000000

open Lean Meta

def mkSharingBench (n : Nat) : MetaM Expr := do
  let nat := mkConst ``Nat
  withLocalDeclD `x nat fun x_fvar => do
    -- d₀ delayed [x] := x
    let d₀Inner ← mkFreshExprMVar nat
    d₀Inner.mvarId!.assign x_fvar
    let d₀Ty ← mkArrow nat nat
    let d₀ ← mkFreshExprMVar d₀Ty (kind := .syntheticOpaque)
    assignDelayedMVar d₀.mvarId! #[x_fvar] d₀Inner.mvarId!

    let mut prev := d₀
    for _ in [:n] do
      let app := mkApp prev x_fvar  -- shared subexpression
      let inner ← mkFreshExprMVar nat
      inner.mvarId!.assign (mkApp2 (mkConst ``Nat.add) app app)
      let dTy ← mkArrow nat nat
      let d ← mkFreshExprMVar dTy (kind := .syntheticOpaque)
      assignDelayedMVar d.mvarId! #[x_fvar] inner.mvarId!
      prev := d

    -- root := fun a => dₙ a
    let rootTy ← mkArrow nat nat
    let root ← mkFreshExprMVar rootTy
    root.mvarId!.assign (Lean.mkLambda `a .default nat (mkApp prev (.bvar 0)))
    return root

-- n=19 is calibrated to take roughly 1s total elaboration time.
-- Use a small n unless TEST_BENCH=1, so that the test suite runs quickly.
run_meta do
  let bench := (← IO.getEnv "TEST_BENCH") == some "1"
  let n := if bench then 19 else 10
  let root ← mkSharingBench n
  discard <| instantiateMVars root
