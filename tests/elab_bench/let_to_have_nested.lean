import Lean

/-!
Benchmark: `Meta.letToHave` in check mode on deeply *nested* (non-telescope) lambdas
whose bodies all reference the outer `let` variable:
`P (let x := c; f (q (fun y₁ => f (q (fun y₂ => …)) x)) x)`.

Every lambda body is open, so `visitLambdaLet` pays one `instantiateRev` on entry and
one `abstract` in `finalize` per binder level: O(n²). The `sym =>` mode implementation
must be near-linear on this family (see `sym_let_to_have_perf.md`).
-/

set_option maxHeartbeats 400000000

axiom S : Type
axiom P : S → Prop
axiom f : S → S → S
axiom q : (S → S) → S
axiom c : S

open Lean Meta

/-- `fun y => f (q (fun y => f (q …) x)) x` where `x` is the `let` variable:
    at nesting depth `k` (under `k` lambdas + the let), `x` is bvar `k+1`.
    Every level mentions `x`, so no subterm is closed. -/
def nest (n : Nat) (depth : Nat) : Expr :=
  match n with
  | 0 => .lam `y (mkConst ``S) (mkApp2 (mkConst ``f) (.bvar 0) (.bvar (depth+1))) .default
  | k+1 => .lam `y (mkConst ``S)
      (mkApp2 (mkConst ``f) (mkApp (mkConst ``q) (nest k (depth+1))) (.bvar (depth+1))) .default

def mkNested (n : Nat) : Expr :=
  let body := mkApp2 (mkConst ``f) (mkApp (mkConst ``q) (nest n 0)) (.bvar 0)
  mkApp (mkConst ``P) (.letE `x (mkConst ``S) (mkConst ``c) body false)

run_meta do
  let bench := (← IO.getEnv "TEST_BENCH") == some "1"
  let ns := if bench then [500, 1000, 2000, 4000] else [20]
  for n in ns do
    let e := mkNested n
    let t0 ← IO.monoNanosNow
    let e' ← Meta.letToHave e
    let t1 ← IO.monoNanosNow
    if bench then
      IO.println s!"nested n={n}: {(t1-t0).toFloat/1e6} ms"
    unless e'.appArg!.isLet && e'.appArg!.letNondep! do
      throwError "expected the let to become a have"
