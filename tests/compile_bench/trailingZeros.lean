module
import Init.Data.Dyadic.Basic

/-! Benchmark arbitrary-precision trailing-zero counting and dyadic normalization (#15264). -/

public def main : IO Unit := do
  let bench := (← IO.getEnv "TEST_BENCH") == some "1"
  let scale := if bench then 1048576 else 1024
  for oddBits in [0, scale] do
    let odd := if oddBits == 0 then 3 else (1 <<< oddBits) + 1
    for zeros in [0, scale, 4 * scale] do
      for extra in [:100] do
        let k := zeros + extra
        let n := odd <<< k
        unless n.trailingZeros == k do
          throw <| IO.userError "incorrect natural trailing-zero count"
        for i in [(n : Int), -(n : Int)] do
          match Dyadic.ofIntWithPrec i 0 with
          | .zero => throw <| IO.userError "unexpected zero"
          | .ofOdd coefficient prec _ =>
            unless coefficient.natAbs == odd && prec == -(k : Int) do
              throw <| IO.userError "incorrect dyadic normalization"
