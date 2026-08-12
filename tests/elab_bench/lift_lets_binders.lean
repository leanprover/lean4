import Lean

/-!
Benchmark: `Meta.liftLets` on nested binders with binder-dependent `let`s
`fun y₁ => let a₁ := g y₁; fun y₂ => let a₂ := f a₁ (g y₂); …; let z := c; f aₙ z`.

Each `aᵢ` depends on `yᵢ` and cannot be lifted past it; only the innermost `z` lifts to
the top. In `lift` mode `Meta.liftLets` extracts every `let` temporarily, and
every binder exit runs `flushDecls`, which rescans all pending declarations and rebuilds
the body with `abstract` — O(n) work per binder exit, O(n²) total.
-/

set_option maxHeartbeats 400000000

axiom S : Type
axiom f : S → S → S
axiom g : S → S
axiom c : S

open Lean Meta

/-- `fun y₁ => let a₁ := g y₁; fun y₂ => let a₂ := f a₁ (g y₂); …; let z := c; f aₙ z` -/
partial def mkBinders (n : Nat) : MetaM Expr := go n none #[] #[]
where
  go (k : Nat) (prev? : Option Expr) (ys as : Array Expr) : MetaM Expr := do
    let Sc : Expr := mkConst ``S
    let fc : Expr := mkConst ``f
    let gc : Expr := mkConst ``g
    let cc : Expr := mkConst ``c
    if k == 0 then
      withLetDecl `z Sc cc fun z => do
        let body := match prev? with
          | some p => mkApp2 fc p z
          | none   => mkApp gc z
        let mut e ← mkLetFVars #[z] body
        for i in [0:ys.size] do
          let j := ys.size - i - 1
          e ← mkLetFVars #[as[j]!] e
          e ← mkLambdaFVars #[ys[j]!] e
        return e
    else
      withLocalDeclD `y Sc fun y => do
        let v := match prev? with
          | some p => mkApp2 fc p (mkApp gc y)
          | none   => mkApp gc y
        withLetDecl `a Sc v fun a =>
          go (k-1) (some a) (ys.push y) (as.push a)

def countTopLets : Expr → Nat
  | .letE _ _ _ b _ => countTopLets b + 1
  | _ => 0

run_meta do
  let bench := (← IO.getEnv "TEST_BENCH") == some "1"
  let ns := if bench then [250, 500, 1000] else [10]
  for n in ns do
    let e ← mkBinders n
    let t0 ← IO.monoNanosNow
    let e' ← Meta.liftLets e
    let t1 ← IO.monoNanosNow
    if bench then
      IO.println s!"binders n={n}: {(t1-t0).toFloat/1e6} ms"
    unless countTopLets e' == 1 do
      throwError "expected 1 top-level let after lifting, got {countTopLets e'}"
