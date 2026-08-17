import Lean

/-!
Benchmark: `Meta.liftLets` on a maximally shared `let` value
`fun yo y₁ … yₘ => let a := dup d (g yo); f a (g yₘ)`, where `dup d s` is a balanced
application tree of depth `d` built with pointer sharing: tree size `2^d`, DAG size `d+1`.

The `let` value mentions `yo` (so the `hasFVar` bit is set on every node) but none of the
inner binders. At each of the `m` inner binder exits, `flushDecls` runs `hasAnyFVar` on
the value; the answer is `false`, and since `hasAnyFVar` has no visited-cache, the
traversal visits the entire `2^d` tree. Time quadruples for every +2 in `d` while the
term's DAG grows by one node per level.
-/

set_option maxHeartbeats 400000000

axiom S : Type
axiom f : S → S → S
axiom g : S → S

open Lean Meta

/-- Balanced application tree of depth `d` over `s`, built with pointer sharing. -/
def dup (d : Nat) (s : Expr) : Expr :=
  match d with
  | 0 => s
  | k+1 => let e := dup k s; mkApp2 (mkConst ``f) e e

/-- `fun yo y₁ … yₘ => let a := dup d (g yo); f a (g yₘ)` -/
partial def mkDag (d m : Nat) : MetaM Expr := do
  let Sc : Expr := mkConst ``S
  let fc : Expr := mkConst ``f
  let gc : Expr := mkConst ``g
  withLocalDeclD `yo Sc fun yo => do
    let v := dup d (mkApp gc yo)
    let rec go (k : Nat) (ys : Array Expr) : MetaM Expr := do
      if k == 0 then
        withLetDecl `a Sc v fun a => do
          let body := mkApp2 fc a (mkApp gc ys.back!)
          let e ← mkLetFVars #[a] body
          mkLambdaFVars (#[yo] ++ ys) e
      else
        withLocalDeclD `y Sc fun y => go (k-1) (ys.push y)
    go m #[]

run_meta do
  let bench := (← IO.getEnv "TEST_BENCH") == some "1"
  let ds := if bench then [16, 18, 20, 22] else [6]
  let m := if bench then 8 else 4
  for d in ds do
    let e ← mkDag d m
    let t0 ← IO.monoNanosNow
    let e' ← Meta.liftLets e
    let t1 ← IO.monoNanosNow
    if bench then
      IO.println s!"dag d={d} m={m}: {(t1-t0).toFloat/1e6} ms"
    -- `a` should have been lifted from below the `m` inner binders to just below `yo`.
    unless e'.isLambda && e'.bindingBody!.isLet do
      throwError "expected `fun yo => let a := …` after lifting"
