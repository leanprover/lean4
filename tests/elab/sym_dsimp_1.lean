import Lean

/-! # Tests for `Sym.dsimp` (programmatic API)

`Sym.dsimp` has no surface syntax yet — these tests exercise it directly via
`SymM`. Each test declares an input `def t_xxx := <term>` and uses
`#guard_msgs in #eval check ...` to verify the simplified form. -/

open Lean Meta Sym Sym.DSimp

/-- Retrieve the body of a `def`. -/
private def getBody (declName : Name) : MetaM Expr := do
  let some e := (← getConstInfo declName).value? | throwError "not a definition"
  return e

/-- Run `Sym.dsimp` on the body of `declName` and log the result. -/
private def check (declName : Name) (methods : Methods := {}) : MetaM Unit := do
  let e ← getBody declName
  let r ← SymM.run do
    Sym.dsimp (← Sym.shareCommon e) (methods := methods)
  logInfo m!"{r}"
  assert! (← isDefEq e r)

/-- A `DSimproc` rewriting `0 + n` to `n` on `Nat` If `n` is a numeral. -/
private def zeroAddRw : DSimproc := fun e => do
  let_expr HAdd.hAdd _ _ _ _ a b := e | return .rfl
  unless a == mkNatLit 0 do return .rfl
  let .some _ ← getNatValue? b | return .rfl
  return .step b

/-- A `DSimproc` rewriting `n + 0` to `n` on `Nat`. -/
private def addZeroRw : DSimproc := fun e => do
  let_expr HAdd.hAdd _ _ _ _ a b := e | return .rfl
  unless b == mkNatLit 0 do return .rfl
  return .step a

/-! ## 1. Identity: with no `pre`/`post`, `dsimp` returns the input unchanged -/

def t_id : Nat := 0 + 1

/-- info: 0 + 1 -/
#guard_msgs in #eval check ``t_id

/-! ## 2. `beta` reduction supplied via `pre` -/

def t_beta : Nat := (fun x : Nat => x + 1) 5

/-- info: 5 + 1 -/
#guard_msgs in #eval check ``t_beta (methods := { pre := beta })

/-! ## 3. `beta` fires inside a lambda body -/

def t_beta_lambda : Nat → Nat := fun y => (fun x : Nat => x) y

-- Output uses `x` rather than `y`: `Sym.shareCommon` is alpha-aware, so the
-- post-beta `fun y => y` is unified with the input's `fun x => x`.
/-- info: fun x => x -/
#guard_msgs in #eval check ``t_beta_lambda (methods := { pre := beta })

/-! ## 4. Custom `post` simproc rewrites at the root -/

def t_zero_add : Nat := 0 + 5

/-- info: 5 -/
#guard_msgs in #eval check ``t_zero_add (methods := { post := zeroAddRw })

/-! ## 5. Application descent: `dsimp` rewrites a non-head argument -/

def t_succ : Nat := Nat.succ (0 + 5)

/-- info: Nat.succ 5 -/
#guard_msgs in #eval check ``t_succ (methods := { post := zeroAddRw })

/-! ## 6. Repeated rewrites: `0 + (0 + 5)` reduces to `5` -/

def t_nested : Nat := 0 + (0 + 5)

/-- info: 5 -/
#guard_msgs in #eval check ``t_nested (methods := { post := zeroAddRw })

/-! ## 7. Lambda descent: `fun y => 0 + y` becomes `fun y => y` -/

def t_lam : Nat → Nat := fun _ => 0 + 5

/-- info: fun x => 5 -/
#guard_msgs in #eval check ``t_lam (methods := { post := zeroAddRw })

/-! ## 8. Forall descent: simplification reaches under `∀` -/

def t_forall : Prop := ∀ y : Nat, 0 + 5 = y

/-- info: ∀ (y : Nat), 5 = y -/
#guard_msgs in #eval check ``t_forall (methods := { post := zeroAddRw })

/-! ## 9. Let descent: both the value and the body are simplified -/

def t_let : Nat := let z : Nat := 0 + 7; z + 0

-- The elaborator marks `z` as `nondep` (since the body doesn't depend on its
-- value at the type level), so the pretty printer shows `have` rather than `let`.
/--
info: have z := 7;
z
-/
#guard_msgs in #eval check ``t_let (methods := { post := zeroAddRw >> addZeroRw })

/-! ## 10. `>>` combinator: chained simprocs fire on the same subterm -/

def t_chain : Nat → Nat := fun x => (x + 0) + 0

/-- info: fun x => x -/
#guard_msgs in #eval check ``t_chain (methods := { post := addZeroRw })

/-! ## 11. `<|>` combinator: second simproc fires when the first does not -/

def t_orelse : Nat → Nat := fun x => x + 0

/-- info: fun x => x -/
#guard_msgs in #eval check ``t_orelse (methods := { post := zeroAddRw <|> addZeroRw })

/-! ## 12. `done = true` on `.rfl`: `pre` stops descent without rewriting -/

def t_done_rfl : Nat := 0 + (0 + 5)

private def stopHere : DSimproc := fun _ => return .rfl true

/-- info: 0 + (0 + 5) -/
#guard_msgs in
#eval check ``t_done_rfl (methods := { pre := stopHere, post := zeroAddRw })

/-! ## 13. `done = true` on `.step`: simplified result is not re-processed -/

def t_done_step : Nat := 0 + 0

/-- Custom `pre` that returns `0` with `done = true`; `post` must not re-fire. -/
private def replaceWithZero : DSimproc := fun _ => return .step (mkNatLit 0) true

/-- info: 0 -/
#guard_msgs in
#eval check ``t_done_step (methods := { pre := replaceWithZero, post := zeroAddRw })
