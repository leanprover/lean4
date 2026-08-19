import Lean

/-!
Benchmark: `Meta.liftLets` on a plain `let` chain
`P (let x₁ := c; let x₂ := f x₁ c; …; let xₙ := f xₙ₋₁ c; xₙ)`.

All `let`s are lifted to the top of the term. `Meta.liftLets` is O(n²):
each `let` costs one `instantiate1` over the remaining body, and the final
`mkLetDecls` folds `abstract` over the result once per declaration.
-/

set_option maxHeartbeats 400000000

axiom S : Type
axiom P : S → Prop
axiom f : S → S → S
axiom c : S

open Lean Meta

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
  let ns := if bench then [500, 1000, 2000] else [15]
  for n in ns do
    let e := mkApp (mkConst ``P) (mkChain n)
    let t0 ← IO.monoNanosNow
    let e' ← Meta.liftLets e
    let t1 ← IO.monoNanosNow
    if bench then
      IO.println s!"chain n={n}: {(t1-t0).toFloat/1e6} ms"
    unless countTopLets e' == n do
      throwError "expected {n} top-level lets after lifting, got {countTopLets e'}"
