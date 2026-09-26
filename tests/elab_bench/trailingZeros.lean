module
import Init.Data.Nat.Bitwise.Lemmas
public meta import Lean

/-! Benchmark kernel reduction of trailing-zero counting on large naturals (#15264). -/

-- Large benchmark inputs need more recursive block steps than the default limit allows.
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option Elab.async false

open Lean Elab Command in
elab "bench_trailing_zeros" : command => do
  let bench := (← IO.getEnv "TEST_BENCH") == some "1"
  let scale := if bench then 4096 else 64
  let repetitions := if bench then 100 else 3
  for oddBits in [0, 16 * scale] do
    let odd := if oddBits == 0 then 3 else (1 <<< oddBits) + 1
    for k in [scale, 16 * scale + 1] do
      let n := odd <<< k
      let lhs := mkApp (mkConst ``Nat.trailingZeros) (mkNatLit n)
      let type := mkApp3 (mkConst ``Eq [.succ .zero]) (mkConst ``Nat) lhs (mkNatLit k)
      let value := mkApp2 (mkConst ``Eq.refl [.succ .zero]) (mkConst ``Nat) lhs
      for r in [:repetitions] do
        let name := Name.mkSimple s!"trailingZeros_{oddBits}_{k}_{r}"
        -- Checking this proof forces kernel reduction without prior elaborator reduction.
        liftCoreM <| addDecl <| .thmDecl { name, levelParams := [], type, value }

bench_trailing_zeros
