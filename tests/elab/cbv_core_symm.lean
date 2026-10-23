import Lean

/-!
Tests that `cbv` can be run on terms from within a user-defined `SymM` session via the public
`Lean.Meta.Tactic.Cbv.cbvCore`, and from a user-driven `SimpM` session via `mkCbvMethods` and
`cbvPre`/`cbvPost`.
-/

open Lean Meta Sym

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- Evaluates `e` with `cbvCore`, prints the result, and kernel-checks the proof. -/
def test (declName : Name) (e : Expr) : SymM Unit := do
  let e ← preprocessExpr e
  match (← Tactic.Cbv.cbvCore e) with
  | .rfl .. => logInfo m!"{e}: no change"
  | .step e' h .. =>
    addDecl <| .thmDecl { name := declName, levelParams := [], type := ← mkEq e e', value := h }
    logInfo m!"{e} ==> {e'}"

/-- info: fib 10 ==> 55 -/
#guard_msgs in
run_meta SymM.run do
  test `fib10 (mkApp (mkConst ``fib) (mkNatLit 10))

def xs := [1, 2, 3].map (· + 1)
def ys := [1, 2, 3].reverse

-- Multiple evaluations in one session share the same `SymM` state.
/--
info: xs ==> [2, 3, 4]
---
info: ys ==> [3, 2, 1]
-/
#guard_msgs in
run_meta SymM.run do
  test `xs_eq (mkConst ``xs)
  test `ys_eq (mkConst ``ys)

/-! Driving `SimpM.run'` directly with `mkCbvMethods`, evaluating several terms in one session. -/

/--
info: xs ==> [2, 3, 4]
---
info: ys ==> [3, 2, 1]
-/
#guard_msgs in
run_meta SymM.run do
  -- `preprocessExpr` relies on the checks that `withoutShareCommonChecks` disables.
  let es ← [``xs, ``ys].mapM (preprocessExpr <| mkConst ·)
  withoutShareCommonChecks do
    let methods := Tactic.Cbv.mkCbvMethods (← Tactic.Cbv.getCbvSimprocs)
    Simp.SimpM.run' (methods := methods) do
      for e in es do
        let .step e' .. ← Simp.simp e | throwError "no progress on {e}"
        logInfo m!"{e} ==> {e'}"

/-! Composing `cbvPre`/`cbvPost` with a user simproc that keeps `blocked` applications unevaluated. -/

def blocked (n : Nat) : Nat := n
def zs := [fib 3, blocked (fib 2)]

/-- info: zs ==> [2, blocked (fib 2)] -/
#guard_msgs in
run_meta SymM.run do
  let e ← preprocessExpr (mkConst ``zs)
  withoutShareCommonChecks do
    let simprocs ← Tactic.Cbv.getCbvSimprocs
    let keepBlocked : Sym.Simp.Simproc := fun e =>
      return if e.isAppOfArity ``blocked 1 then .rfl (done := true) else .rfl
    let methods : Sym.Simp.Methods :=
      { pre := keepBlocked <|> Tactic.Cbv.cbvPre simprocs, post := Tactic.Cbv.cbvPost simprocs }
    let .step e' h .. ← Simp.SimpM.run' (methods := methods) (Simp.simp e) | throwError "no progress"
    addDecl <| .thmDecl { name := `zs_eq, levelParams := [], type := ← mkEq e e', value := h }
    logInfo m!"{e} ==> {e'}"
