module

import Lean

/-!
Regression test for #15985: inferring types of freshly rebuilt application chains should not
spend quadratic time comparing expressions against cached copies. No matcher reduction is needed.
-/

opaque f : Nat → Nat := fun x => x

open Lean Meta

set_option maxHeartbeats 0
set_option maxRecDepth 100000

private def repeatedInferCost (n : Nat) : MetaM Nat := do
  resetCache
  let fn := mkConst ``f
  let mut costs := #[]
  for _ in [0:2] do
    let start ← IO.getNumHeartbeats
    let mut e := mkNatLit 0
    for _ in [0:n] do
      e := mkApp fn e
      unless (← inferType e).isConstOf ``Nat do
        throwError "unexpected type"
    costs := costs.push ((← IO.getNumHeartbeats) - start)
  return costs[1]!

run_meta do
  let n := if (← IO.getEnv "TEST_BENCH") == some "1" then 32768 else 4096
  let small ← repeatedInferCost n
  let large ← repeatedInferCost (2 * n)
  unless large ≤ 3 * small do
    throwError "doubling repeated type inference used {large} heartbeats after {small}"
