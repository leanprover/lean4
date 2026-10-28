module

import Lean

/-!
Regression test for #15985: repeated matcher reductions with freshly built accumulators should
not perform quadratic structural comparisons in the type-inference cache.
-/

open Lean Meta

set_option maxRecDepth 100000

private def repeatedMatcherCost (n : Nat) : MetaM Nat := do
  resetCache
  let bytes := mkApp (mkConst ``List [0]) (mkConst ``UInt8)
  let byteArray := mkConst ``ByteArray
  let motive := mkLambda `xs .default bytes <|
    mkLambda `acc .default byteArray byteArray
  let nil := mkApp (mkConst ``List.nil [0]) (mkConst ``UInt8)
  let nilAlt := mkLambda `acc .default byteArray (mkBVar 0)
  let consAlt := mkLambda `b .default (mkConst ``UInt8) <|
    mkLambda `bs .default bytes nilAlt
  let matcher := mkConst ``List.toByteArray.match_1 [1]
  let byte := toExpr (0 : UInt8)
  let mut costs := #[]
  for _ in [0:2] do
    let start ← IO.getNumHeartbeats
    let mut acc := mkConst ``ByteArray.empty
    for _ in [0:n] do
      let e := mkAppN matcher #[motive, nil, acc, nilAlt, consAlt]
      let .reduced result ← reduceMatcher? e | throwError "matcher did not reduce"
      unless result == acc do throwError "unexpected matcher result"
      acc := mkApp2 (mkConst ``ByteArray.push) acc byte
    costs := costs.push ((← IO.getNumHeartbeats) - start)
  return costs[1]!

run_meta do
  let n := if (← IO.getEnv "TEST_BENCH") == some "1" then 32768 else 4096
  let small ← repeatedMatcherCost n
  let large ← repeatedMatcherCost (2 * n)
  unless large ≤ 3 * small do
    throwError "doubling repeated matcher reduction used {large} heartbeats after {small}"
