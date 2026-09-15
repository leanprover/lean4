module
import Lean
public meta import Lean

/-! Kernel reduction of modular powers at cryptographic operand sizes. -/

open Lean in
run_cmd do
  let bench := (← IO.getEnv "TEST_BENCH") == some "1"
  let cases := if bench then [31, 61, 127, 255, 521, 1024] else [255]
  let env ← getEnv
  let ready ← IO.mkRef env.toKernelEnv
  let env := Environment.ofKernelEnv (← ready.get)
  for bits in cases do
    let m := 2 ^ bits - 19
    let e := m - 1
    let result := Nat.powMod 2 e m
    let value := mkRawNatLit result
    let lhs := mkApp3 (mkConst ``Nat.powMod) (mkRawNatLit 2) (mkRawNatLit e) (mkRawNatLit m)
    let type := mkApp3 (mkConst ``Eq [.succ .zero]) (mkConst ``Nat) lhs value
    let refl := mkApp2 (mkConst ``Eq.refl [.succ .zero]) (mkConst ``Nat) value
    let proof := mkApp (mkLambda `h .default type (mkBVar 0)) refl
    let input ← IO.mkRef (env, proof)
    let (env, proof) ← input.get
    let start ← IO.monoNanosNow
    let checked ← IO.mkRef (Kernel.check env {} proof)
    let checked ← checked.get
    let stop ← IO.monoNanosNow
    match checked with
    | .error _ => throwError "kernel reduction disagrees with native powMod"
    | .ok _ => pure ()
    if bench then IO.println s!"powMod {bits} bits: {stop - start} ns"
