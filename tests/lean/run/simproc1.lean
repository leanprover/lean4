import Lean.Meta.Tactic.Simp.BuiltinSimprocs

def foo (x : Nat) : Nat :=
  x + 10

open Lean Meta

simproc reduceFoo (foo _) := fun e => OptionT.run do
  guard (e.isAppOfArity ``foo 1)
  let n ← Nat.fromExpr? e.appArg!
  return .done { expr := mkNatLit (n+10) }

example : x + foo 2 = 12 + x := by
  set_option simprocs false in fail_if_success simp
  simp_arith

example : x + foo 2 = 12 + x := by
  -- `simp only` must not use the default simproc set
  fail_if_success simp only
  simp_arith

example : x + foo 2 = 12 + x := by
  -- `simp only` does not use the default simproc set, but we can provide simprocs as arguments
  simp only [reduceFoo]
  simp_arith

example : x + foo 2 = 12 + x := by
  -- We can use `-` to disable `simproc`s
  fail_if_success simp [-reduce_foo]
  simp_arith
