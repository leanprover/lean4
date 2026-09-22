module
import Init.Data.BitVec.Lemmas

/-! Benchmark zero counting across bitvector widths and natural-number representations. -/

public def main : IO Unit := do
  let bench := (← IO.getEnv "TEST_BENCH") == some "1"
  let width := if bench then 65536 else 256
  let repetitions := if bench then 10000 else 10
  for w in [0, 8, 64, width] do
    for r in [:repetitions] do
      let odd := 2 * r + 1
      for k in [0, w / 2, w - 1] do
        let x := BitVec.ofNat w (odd <<< k)
        let leading := x.clz.toNat
        let trailing := x.ctz.toNat
        unless leading ≤ w && trailing ≤ w && (x != 0 || (leading == w && trailing == w)) do
          throw <| IO.userError "invalid zero count"
