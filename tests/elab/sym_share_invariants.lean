import Lean

/-! # Tests for `Sym.shareCommon` invariant enforcement

`Sym.shareCommon` maintains the `SymM` invariants that reducible constants have
been unfolded and kernel projections folded. These tests exercise the check and
repair path directly via `SymM`: terms violating the invariants are repaired
before entering the table of maximally shared terms, and already-admitted terms
are not re-processed. -/

open Lean Meta Sym

abbrev myAbbrev (x : Nat) : Nat := x + 1

structure Point where
  x : Nat
  y : Nat

/-- Asserts `e` contains no reducible constant that `unfoldReducible` should have unfolded. -/
private def assertNoReducible (e : Expr) : MetaM Unit := do
  let env ← getEnv
  let bad? := e.find? fun e =>
    if let .const declName _ := e then
      isUnfoldReducibleCandidate env declName
    else
      false
  assert! bad?.isNone

/-- Asserts `e` contains no kernel projection. -/
private def assertNoProj (e : Expr) : MetaM Unit := do
  assert! (e.find? Expr.isProj).isNone

/-! ## Reducible constants are unfolded by `shareCommon` -/

/-- info: 5 + 1 -/
#guard_msgs in
run_meta SymM.run do
  let e := mkApp (mkConst ``myAbbrev) (mkNatLit 5)
  let e ← shareCommon e
  assertNoReducible e
  e.checkMaxShared
  logInfo m!"{e}"

/-! ## ... also under binders -/

/-- info: fun x => x + 1 -/
#guard_msgs in
run_meta SymM.run do
  let e := mkLambda `x .default (mkConst ``Nat) (mkApp (mkConst ``myAbbrev) (mkBVar 0))
  let e ← shareCommon e
  assertNoReducible e
  e.checkMaxShared
  logInfo m!"{e}"

/-! ## Kernel projections are folded by `shareCommon`; the projection function
       `Point.x` is reducible but must **not** be unfolded (it would expose the
       kernel projection again) -/

/-- info: { x := 1, y := 2 }.x -/
#guard_msgs in
run_meta SymM.run do
  let p := mkApp2 (mkConst ``Point.mk) (mkNatLit 1) (mkNatLit 2)
  let e := Expr.proj ``Point 0 p
  let e ← shareCommon e
  assertNoProj e
  assert! (e.find? fun e => e.isConstOf ``Point.x).isSome
  e.checkMaxShared
  logInfo m!"{e}"

/-! ## Both violations in a single term -/

/-- info: { x := 5 + 1, y := 2 }.y -/
#guard_msgs in
run_meta SymM.run do
  let p := mkApp2 (mkConst ``Point.mk) (mkApp (mkConst ``myAbbrev) (mkNatLit 5)) (mkNatLit 2)
  let e := Expr.proj ``Point 1 p
  let e ← shareCommon e
  assertNoReducible e
  assertNoProj e
  e.checkMaxShared
  logInfo m!"{e}"

/-! ## `shareCommonInc` repairs too (falls back to the full pass) -/

/-- info: 7 + 1 -/
#guard_msgs in
run_meta SymM.run do
  let seven ← shareCommon (mkNatLit 7)
  let e := mkApp (mkConst ``myAbbrev) seven
  let e ← shareCommonInc e
  assertNoReducible e
  e.checkMaxShared
  logInfo m!"{e}"

/-! ## Checks disabled: `withoutFoldProjsCheck` admits kernel projections (`cbv`/`vcgen` style) -/

/-- info: ok -/
#guard_msgs in
run_meta SymM.run do
  withoutFoldProjsCheck do
    let p := mkApp2 (mkConst ``Point.mk) (mkNatLit 1) (mkNatLit 2)
    let e := Expr.proj ``Point 0 p
    let e ← shareCommon e
    assert! e.isProj
    e.checkMaxShared
    logInfo "ok"

/-! ## Clean terms take the fast path and are unchanged -/

/-- info: Nat.succ 3 -/
#guard_msgs in
run_meta SymM.run do
  let e := mkApp (mkConst ``Nat.succ) (mkNatLit 3)
  let e₁ ← shareCommon e
  let e₂ ← shareCommon e₁
  assert! isSameExpr e₁ e₂
  e₁.checkMaxShared
  logInfo m!"{e₁}"
