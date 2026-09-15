module
meta import Lean

/-! Kernel reduction of modular powers at cryptographic operand sizes. -/

open Lean in
run_cmd do
  let bench := (← IO.getEnv "TEST_BENCH") == some "1"
  let cases := if bench then [31, 61, 127, 255, 512, 521, 1024, 2048, 4096, 8192] else [255]
  let env ← getEnv
  -- Finish pending kernel tasks before timing. The references also prevent hoisting
  -- pure kernel calls across the timer if this code is compiled.
  let ready ← IO.mkRef env.toKernelEnv
  let env := Environment.ofKernelEnv (← ready.get)
  for bits in cases do
    let m := 2 ^ bits - 19
    for largeBase in (if bench && bits ≥ 2048 then [false, true] else [false]) do
      let e := m - 1
      let base := if largeBase then m / 3 else 2
      let result := Nat.powMod base e m
      let value := mkRawNatLit result
      let lhs := mkApp3 (mkConst ``Nat.powMod) (mkRawNatLit base) (mkRawNatLit e) (mkRawNatLit m)
      let type := mkApp3 (mkConst ``Eq [.succ .zero]) (mkConst ``Nat) lhs value
      let refl := mkApp2 (mkConst ``Eq.refl [.succ .zero]) (mkConst ``Nat) value
      let proof := mkApp (mkLambda `h .default type (mkBVar 0)) refl
      let repetitions := if bench then 20 else 1
      let mut total : Nat := 0
      for _ in [:repetitions] do
        let input ← IO.mkRef (env, proof)
        let (env, proof) ← input.get
        let start ← IO.monoNanosNow
        let checked ← IO.mkRef (Kernel.check env {} proof)
        let checked ← checked.get
        let stop ← IO.monoNanosNow
        let _ ← ofExceptKernelException checked
        total := total + (stop - start)
      let suffix := if largeBase then "_large_base" else ""
      IO.println s!"measurement: powmod_kernel_{bits}bit{suffix} {total.toFloat / repetitions.toFloat / 1e6} ms"
