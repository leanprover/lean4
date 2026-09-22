module
import Init.Data.BitVec.Lemmas
public meta import Lean

/-! Benchmark kernel reduction of zero counting on wide bitvectors. -/

-- Leave room for the reduction of the natural-number counters.
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option Elab.async false

open Lean Elab Command in
elab "bench_bitvec_zero_counts" : command => do
  let bench := (← IO.getEnv "TEST_BENCH") == some "1"
  let scale := if bench then 4096 else 64
  let repetitions := if bench then 100 else 3
  for w in [scale, 16 * scale] do
    for k in [0, min 256 (w - 2)] do
      let n := 3 <<< k
      for fn in [``BitVec.ctz, ``BitVec.clz] do
        let input := mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit w) (mkNatLit n)
        let result := if fn == ``BitVec.ctz then k else w - (n.log2 + 1)
        let count := mkApp2 (mkConst fn) (mkNatLit w) input
        let lhs := mkApp2 (mkConst ``BitVec.toNat) (mkNatLit w) count
        let type := mkApp3 (mkConst ``Eq [.succ .zero]) (mkConst ``Nat) lhs (mkNatLit result)
        let value := mkApp2 (mkConst ``Eq.refl [.succ .zero]) (mkConst ``Nat) lhs
        for r in [:repetitions] do
          let name := Name.mkSimple s!"zeroCounts_{fn}_{w}_{k}_{r}"
          -- Checking this proof forces kernel reduction without prior elaborator reduction.
          liftCoreM <| addDecl <| .thmDecl { name, levelParams := [], type, value }

bench_bitvec_zero_counts
