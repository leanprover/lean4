import Lean

/-!
Benchmark: `Sym.letToHave` on the closed-body family of `let_to_have_closed_body.lean`
(one dep-flagged `let` whose big body never mentions the `let` variable).

`Meta.letToHave` fully typechecks the body (~1.2 µs/node); the `SymM` implementation
skips the check entirely — the remaining linear cost is the pointer-cached `hasDepLet`
scan (~0.2 µs/node).
-/

set_option maxHeartbeats 400000000

axiom S : Type
axiom P : S → Prop
axiom f : S → S → S
axiom c : S

open Lean Meta Sym

/-- See `let_to_have_closed_body.lean`. -/
def mkBigBodyClosed (n : Nat) : Expr := Id.run do
  let fc : Expr := mkConst ``f
  let cc : Expr := mkConst ``c
  let mut b := cc
  for _ in [0:n] do
    b := mkApp2 fc b cc
  return mkApp (mkConst ``P) (.letE `x (mkConst ``S) cc b false)

run_meta do
  let bench := (← IO.getEnv "TEST_BENCH") == some "1"
  let ns := if bench then [16000, 64000, 256000] else [20]
  for n in ns do
    let e := mkBigBodyClosed n
    SymM.run do
      let e ← shareCommon e
      let t0 ← IO.monoNanosNow
      let e' ← Sym.letToHave e
      let t1 ← IO.monoNanosNow
      if bench then
        IO.println s!"sym closed_body n={n}: {(t1-t0).toFloat/1e6} ms"
      unless e'.appArg!.isLet && e'.appArg!.letNondep! do
        throwError "expected the let to become a have"
