import Lean

/-!
Tests that `cbv` can be run on terms from within a user-defined `SymM` session via the public
`Lean.Meta.Tactic.Cbv.cbvCore`.
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
