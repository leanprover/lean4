import Lean

/-!
Benchmark: `Sym.letToHave` on the nested-open-lambda family of
`let_to_have_nested.lean` (every lambda body references the outer `let` variable).

`Meta.letToHave` is O(n²) on this family (per-binder instantiate/abstract); the `SymM`
implementation keeps bodies in bound-variable form and is near-linear.
-/

set_option maxHeartbeats 400000000

axiom S : Type
axiom P : S → Prop
axiom f : S → S → S
axiom q : (S → S) → S
axiom c : S

open Lean Meta Sym

/-- See `let_to_have_nested.lean`. -/
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
  let ns := if bench then [500, 1000, 2000, 4000, 8000] else [20]
  for n in ns do
    let e := mkNested n
    SymM.run do
      let e ← shareCommon e
      let t0 ← IO.monoNanosNow
      let e' ← Sym.letToHave e
      let t1 ← IO.monoNanosNow
      if bench then
        IO.println s!"sym nested n={n}: {(t1-t0).toFloat/1e6} ms"
      unless e'.appArg!.isLet && e'.appArg!.letNondep! do
        throwError "expected the let to become a have"
