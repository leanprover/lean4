module
import Init.Data.BitVec.Lemmas

/-! Benchmark zero counting across bitvector widths and natural-number representations. -/

public def main : IO Unit := do
  let bench := (← IO.getEnv "TEST_BENCH") == some "1"
  let width := if bench then 65536 else 256
  let repetitions := if bench then 1000 else 1
  for w in [0, 8, 64, width] do
    let mut inputs : Array (BitVec w) := #[]
    for r in [:100] do
      for k in [0, w / 2, w - 1] do
        inputs := inputs.push (BitVec.ofNat w ((2 * r + 1) <<< k))
    for _ in [:repetitions] do
      for x in inputs do
        let leading := x.clz.toNat
        let trailing := x.ctz.toNat
        unless leading ≤ w && trailing ≤ w && (x != 0 || (leading == w && trailing == w)) do
          throw <| IO.userError "invalid zero count"
