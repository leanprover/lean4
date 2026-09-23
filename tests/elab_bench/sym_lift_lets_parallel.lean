import Lean

/-!
Benchmark: `Sym.liftLets` on the parallel-branches family of `lift_lets_parallel.lean`
(a balanced `f`-application tree whose `m` leaves are distinct independent `let`s).

Each leaf is a closed subterm, so this exercises the closed-subterm cache path of the
`SymM` implementation. Near-linear in the term's DAG size, in contrast to the O(m²)
standard `Meta.liftLets`.
-/

set_option maxHeartbeats 400000000

axiom S : Type
axiom P : S → Prop
axiom f : S → S → S
axiom g : S → S
axiom h : Nat → S

open Lean Meta Sym

/-- Balanced `f`-tree with `m` leaves `let x := h i; g x` (distinct values, no dependencies). -/
def mkParallel (m : Nat) : Expr := Id.run do
  let Sc : Expr := mkConst ``S
  let fc : Expr := mkConst ``f
  let gc : Expr := mkConst ``g
  let hc : Expr := mkConst ``h
  let mut cur := Array.mkEmpty m
  for i in [0:m] do
    cur := cur.push (Expr.letE `x Sc (mkApp hc (mkNatLit i)) (mkApp gc (.bvar 0)) false)
  while cur.size > 1 do
    let mut next := Array.mkEmpty ((cur.size + 1) / 2)
    let mut i := 0
    while i + 1 < cur.size do
      next := next.push (mkApp2 fc cur[i]! cur[i+1]!)
      i := i + 2
    if i < cur.size then
      next := next.push cur[i]!
    cur := next
  return cur[0]!

def countTopLets : Expr → Nat
  | .letE _ _ _ b _ => countTopLets b + 1
  | _ => 0

run_meta do
  let bench := (← IO.getEnv "TEST_BENCH") == some "1"
  let ms := if bench then [2000, 8000, 32000] else [15]
  for m in ms do
    let e := mkApp (mkConst ``P) (mkParallel m)
    SymM.run do
      let e ← shareCommon e
      let t0 ← IO.monoNanosNow
      let e' ← Sym.liftLets e
      let t1 ← IO.monoNanosNow
      if bench then
        IO.println s!"sym parallel m={m}: {(t1-t0).toFloat/1e6} ms"
      unless countTopLets e' == m do
        throwError "expected {m} top-level lets after lifting, got {countTopLets e'}"
