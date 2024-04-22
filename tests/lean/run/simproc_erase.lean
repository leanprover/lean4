import Lean.Meta.Tactic.Simp.BuiltinSimprocs

def foo (x : Nat) : Nat :=
  x + 10

open Lean Meta

/-- doc-comment for reduceFoo -/
simproc reduceFoo (foo _) := fun e => do
  unless e.isAppOfArity ``foo 1 do return .continue
  let some n ← Nat.fromExpr? e.appArg! | return .continue
  return .done { expr := mkNatLit (n+10) }

example : x + foo 2 = 12 + x := by
  simp
  rw [Nat.add_comm]

attribute [-simp] reduceFoo

example : x + foo 2 = 12 + x := by
  fail_if_success simp
  simp [foo]
  rw [Nat.add_comm]

attribute [simp] reduceFoo

example : x + foo 2 = 12 + x := by
  simp
  rw [Nat.add_comm]

example (h : 12 = x) : 10 + 2 = x := by
  simp
  guard_target =ₛ 12 = x
  assumption

attribute [-simp] Nat.reduceAdd

example (h : 12 = x) : 10 + 2 = x := by
  fail_if_success simp
  simp [Nat.reduceAdd]
  guard_target =ₛ 12 = x
  assumption

attribute [simp] Nat.reduceAdd

example (h : 12 = x) : 10 + 2 = x := by
  simp
  guard_target =ₛ 12 = x
  assumption
