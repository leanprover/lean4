import Lean

/-!
Benchmark: `Sym.letToHave` on the `let`-chain family of `let_to_have_chain.lean`
(`P (let x₁ := c; let x₂ := f x₁ c; …; let xₙ := f xₙ₋₁ c; xₙ)`, all flagged dependent).
-/

set_option maxHeartbeats 400000000

axiom S : Type
axiom P : S → Prop
axiom f : S → S → S
axiom c : S

open Lean Meta Sym

/-- See `let_to_have_chain.lean`. -/
def mkChain (n : Nat) : Expr := Id.run do
  let Sc : Expr := mkConst ``S
  let fc : Expr := mkConst ``f
  let cc : Expr := mkConst ``c
  let mut e := Expr.bvar 0
  for _ in [1:n] do
    e := .letE `x Sc (mkApp2 fc (.bvar 0) cc) e false
  return mkApp (mkConst ``P) (.letE `x Sc cc e false)

def countHaves : Expr → Nat
  | .letE _ _ _ b nondep => countHaves b + (if nondep then 1 else 0)
  | .app f a => countHaves f + countHaves a
  | _ => 0

run_meta do
  let bench := (← IO.getEnv "TEST_BENCH") == some "1"
  let ns := if bench then [1000, 2000, 4000, 8000] else [20]
  for n in ns do
    let e := mkChain n
    SymM.run do
      let e ← shareCommon e
      let t0 ← IO.monoNanosNow
      let e' ← Sym.letToHave e
      let t1 ← IO.monoNanosNow
      if bench then
        IO.println s!"sym chain n={n}: {(t1-t0).toFloat/1e6} ms"
      unless countHaves e' == n do
        throwError "expected {n} haves, got {countHaves e'}"
