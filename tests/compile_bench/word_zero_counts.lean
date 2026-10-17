module
import Init.Data.UInt.BitCounts

/-! Benchmark native word zero counts, including the XOR/ctz byte-mismatch pattern. -/

public def main : IO Unit := do
  let bench := (← IO.getEnv "TEST_BENCH") == some "1"
  let repetitions := if bench then 1000000 else 1000
  let mut seed : UInt64 := 0x9e3779b97f4a7c15
  let mut checksum : UInt64 := 0
  for r in [:repetitions] do
    seed := seed * 6364136223846793005 + 1442695040888963407
    let byte := UInt64.ofNat (r % 8)
    let other := seed ^^^ ((seed ||| 1) <<< (8 * byte))
    unless ((seed ^^^ other).ctz >>> 3) == byte do
      throw <| IO.userError "incorrect first differing byte"
    checksum := checksum + seed.clz + seed.ctz + seed.log2
    checksum := checksum + seed.toUInt32.clz.toUInt64 + seed.toUInt32.ctz.toUInt64
    checksum := checksum + seed.toUInt16.clz.toUInt64 + seed.toUInt16.ctz.toUInt64
    checksum := checksum + seed.toUInt8.clz.toUInt64 + seed.toUInt8.ctz.toUInt64
    checksum := checksum + seed.toUSize.clz.toUInt64 + seed.toUSize.ctz.toUInt64
  if checksum == 0 then throw <| IO.userError "empty checksum"
