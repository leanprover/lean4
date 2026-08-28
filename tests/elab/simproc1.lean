import Lean.Meta.Tactic.Simp.BuiltinSimprocs
import Lean.Elab.Command

def foo (x : Nat) : Nat :=
  x + 10

open Lean Meta

/-- doc-comment for reduceFoo -/
simproc reduceFoo (foo _) := fun e => do
  unless e.isAppOfArity ``foo 1 do return .continue
  let some n ← Nat.fromExpr? e.appArg! | return .continue
  return .done { expr := mkNatLit (n+10) }

run_meta do
  guard <| (← findDocString? (← getEnv) ``reduceFoo) = some "doc-comment for reduceFoo "

example : x + foo 2 = 12 + x := by
  set_option simprocs false in fail_if_success simp
  simp +arith

example : x + foo 2 = 12 + x := by
  -- `simp only` must not use the default simproc set
  fail_if_success simp only
  simp +arith

example : x + foo 2 = 12 + x := by
  -- `simp only` does not use the default simproc set, but we can provide simprocs as arguments
  simp only [reduceFoo]
  simp +arith

example : x + foo 2 = 12 + x := by
  -- We can use `-` to disable `simproc`s
  fail_if_success simp [-reduceFoo]
  simp +arith

example (x : Nat) (h : x < 86) : ¬100 ≤ x + 14 := by simp; exact h
