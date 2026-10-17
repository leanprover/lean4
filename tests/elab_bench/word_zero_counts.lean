module
import Init.Data.UInt.BitCounts
public meta import Lean

/-! Benchmark kernel reduction of word counts at small values and worst-case bit positions. -/

set_option Elab.async false
set_option maxHeartbeats 0

open Lean Elab Command in
elab "bench_word_zero_counts" : command => do
  let bench := (← IO.getEnv "TEST_BENCH") == some "1"
  let repetitions := if bench then 100 else 3
  for (typeName, width) in [("UInt8", 8), ("UInt16", 16), ("UInt32", 32), ("UInt64", 64)] do
    let name := Name.mkSimple typeName
    for n in [0, 1, 3, 1 <<< (width - 1), (1 <<< width) - 1] do
      for op in ["ctz", "clz"] do
        let input := mkApp (mkConst (name ++ `ofNat)) (mkNatLit n)
        let result := if n == 0 then width else
          if op == "ctz" then n.trailingZeros else width - (n.log2 + 1)
        let count := mkApp (mkConst (name ++ Name.mkSimple op)) input
        let lhs := mkApp (mkConst (name ++ `toNat)) count
        let type := mkApp3 (mkConst ``Eq [.succ .zero]) (mkConst ``Nat) lhs (mkNatLit result)
        let value := mkApp2 (mkConst ``Eq.refl [.succ .zero]) (mkConst ``Nat) lhs
        for r in [:repetitions] do
          let declName := Name.mkSimple s!"wordCount_{name}_{op}_{n}_{r}"
          -- Submit the reflexivity proof directly, forcing the kernel to reduce the counter.
          liftCoreM <| addDecl <| .thmDecl { name := declName, levelParams := [], type, value }

bench_word_zero_counts
