import Lean

/-!
Benchmark: `Meta.liftLets` on a single `let` buried under a deep application spine
`P (f (f (… (f (let x := c; g x) c) …) c) c)` with `m` spine nodes.

The single `let` is lifted past the whole spine. `Meta.liftLets` is O(m²):
the `containsLet` skip-check re-traverses the whole subtree at every visited node, and
each node additionally pays an `isProof` (`inferType`) call.
-/

set_option maxHeartbeats 400000000

axiom S : Type
axiom P : S → Prop
axiom f : S → S → S
axiom g : S → S
axiom c : S

open Lean Meta

/-- `f (f (… (f (let x := c; g x) c) …) c) c` with `m` spine nodes. -/
def mkSpine (m : Nat) : Expr := Id.run do
  let Sc : Expr := mkConst ``S
  let fc : Expr := mkConst ``f
  let gc : Expr := mkConst ``g
  let cc : Expr := mkConst ``c
  let mut e := Expr.letE `x Sc cc (mkApp gc (.bvar 0)) false
  for _ in [0:m] do
    e := mkApp2 fc e cc
  return e

def countTopLets : Expr → Nat
  | .letE _ _ _ b _ => countTopLets b + 1
  | _ => 0

run_meta do
  let bench := (← IO.getEnv "TEST_BENCH") == some "1"
  let ms := if bench then [1000, 2000, 4000] else [20]
  for m in ms do
    let e := mkApp (mkConst ``P) (mkSpine m)
    let t0 ← IO.monoNanosNow
    let e' ← Meta.liftLets e
    let t1 ← IO.monoNanosNow
    if bench then
      IO.println s!"spine m={m}: {(t1-t0).toFloat/1e6} ms"
    unless countTopLets e' == 1 do
      throwError "expected 1 top-level let after lifting, got {countTopLets e'}"
