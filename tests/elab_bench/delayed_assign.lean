import Lean

/-!
This benchmark exercises `instantiateMVars` on a large metavariable
assignment graph with many nested delayed assignments.

We construct a goal of the form
  `∀ x₁ … xₙ, ((0 ≤ x₁) ∧ … ∧ True) ∧ … ∧ ((0 ≤ xₙ) ∧ … ∧ True)`
as a single mvar, solve it (creating O(n²) delayed mvars), and then
call `instantiateMVars` to fully resolve the result.
-/

set_option maxHeartbeats 40000000

open Lean Meta

def mkLE (i : Nat) : Expr :=
  mkNatLE (mkNatLit 0) (mkBVar i)

partial def solve (mvarId : MVarId) : MetaM Unit := do
  let type ← instantiateMVars (← mvarId.getType)
  if type.isForall then
    let (_, mvarId) ← mvarId.intro1
    solve mvarId
  else if type.isAppOf ``And then
    let [mvarId₁, mvarId₂] ← mvarId.applyConst ``And.intro | failure
    solve mvarId₁
    solve mvarId₂
  else if type.isAppOf ``LE.le then
    let [] ← mvarId.applyConst ``Nat.zero_le | failure
  else
    let [] ← mvarId.applyConst ``True.intro | failure

def mkBench (n : Nat) : MetaM MVarId := do
  let type := mkType n
  return (← mkFreshExprSyntheticOpaqueMVar type).mvarId!
where
  mkResultType (i : Nat) : Expr :=
    match i with
    | 0 => mkConst ``True
    | i+1 => mkAnd (mkLE i) (mkResultType i)

  mkType (i : Nat) : Expr :=
    match i with
    | 0 => mkResultType n
    | i+1 => .forallE `x Nat.mkType (mkAnd (mkType i) (mkLE (n - i - 1))) .default

-- n=200 is calibrated to take roughly 1s total elaboration time.
-- Use a small n unless TEST_BENCH=1, so that the test suite runs quickly.
run_meta do
  let bench := (← IO.getEnv "TEST_BENCH") == some "1"
  let n := if bench then 200 else 50
  let mvarId ← mkBench n
  solve mvarId
  discard <| instantiateMVars (mkMVar mvarId)
