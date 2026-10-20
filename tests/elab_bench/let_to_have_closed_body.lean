import Lean

/-!
Benchmark: the check-mode tax of `Meta.letToHave` — one dep-flagged `let` whose big body
never mentions the `let` variable: `P (let x := c; f (f … (f c c) …) c)`.

The body is closed, so it cannot create a dependence, yet the current implementation
fully typechecks all of it (`canSkip` requires `approxDepth ≤ 2`). The `sym =>` mode
implementation must skip it in O(1) (see `sym_let_to_have_perf.md`).
-/

set_option maxHeartbeats 400000000

axiom S : Type
axiom P : S → Prop
axiom f : S → S → S
axiom c : S

open Lean Meta

/-- `P (let x := c; f-application chain of length n, closed body not using x)` -/
def mkBigBodyClosed (n : Nat) : Expr := Id.run do
  let fc : Expr := mkConst ``f
  let cc : Expr := mkConst ``c
  let mut b := cc
  for _ in [0:n] do
    b := mkApp2 fc b cc
  return mkApp (mkConst ``P) (.letE `x (mkConst ``S) cc b false)

run_meta do
  let bench := (← IO.getEnv "TEST_BENCH") == some "1"
  let ns := if bench then [4000, 8000, 16000] else [20]
  for n in ns do
    let e := mkBigBodyClosed n
    let t0 ← IO.monoNanosNow
    let e' ← Meta.letToHave e
    let t1 ← IO.monoNanosNow
    if bench then
      IO.println s!"closed_body n={n}: {(t1-t0).toFloat/1e6} ms"
    unless e'.appArg!.isLet && e'.appArg!.letNondep! do
      throwError "expected the let to become a have"
