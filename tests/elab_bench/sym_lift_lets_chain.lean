import Lean

/-!
Benchmark: `Sym.liftLets` on the `let`-chain family of `lift_lets_chain.lean`
(`P (let x₁ := c; let x₂ := f x₁ c; …; let xₙ := f xₙ₋₁ c; xₙ)`).

The `SymM` implementation is near-linear in the term's DAG size, in contrast to the
O(n²) standard `Meta.liftLets`.
-/

set_option maxHeartbeats 400000000

axiom S : Type
axiom P : S → Prop
axiom f : S → S → S
axiom c : S

open Lean Meta Sym

/-- `let x₁ := c; let x₂ := f x₁ c; …; let xₙ := f xₙ₋₁ c; xₙ` -/
def mkChain (n : Nat) : Expr := Id.run do
  let Sc : Expr := mkConst ``S
  let fc : Expr := mkConst ``f
  let cc : Expr := mkConst ``c
  let mut e := Expr.bvar 0
  for _ in [1:n] do
    e := .letE `x Sc (mkApp2 fc (.bvar 0) cc) e false
  return .letE `x Sc cc e false

def countTopLets : Expr → Nat
  | .letE _ _ _ b _ => countTopLets b + 1
  | _ => 0

run_meta do
  let bench := (← IO.getEnv "TEST_BENCH") == some "1"
  let ns := if bench then [2000, 8000, 32000] else [15]
  for n in ns do
    let e := mkApp (mkConst ``P) (mkChain n)
    SymM.run do
      let e ← shareCommon e
      let t0 ← IO.monoNanosNow
      let e' ← Sym.liftLets e
      let t1 ← IO.monoNanosNow
      if bench then
        IO.println s!"sym chain n={n}: {(t1-t0).toFloat/1e6} ms"
      unless countTopLets e' == n do
        throwError "expected {n} top-level lets after lifting, got {countTopLets e'}"
