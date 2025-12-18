import Lean

def foo (x : Nat) := x + 1

open Lean Meta Simp
dsimproc reduceFoo (foo _) := fun e => do
  let_expr foo a ← e | return .continue
  let some n ← getNatValue? a | return .continue
  return .done (toExpr (n+1))

example (h : 3 = x) : foo 2 = x := by
  simp
  guard_target =ₛ 3 = x
  assumption

example (h : 3 = x) : foo 2 = x := by
  fail_if_success simp [-reduceFoo]
  fail_if_success simp only
  simp only [reduceFoo]
  guard_target =ₛ 3 = x
  assumption

def bla (x : Nat) := 2*x

dsimproc_decl reduceBla (bla _) := fun e => do
  let_expr bla a ← e | return .continue
  let some n ← getNatValue? a | return .continue
  return .done (toExpr (2*n))

example (h : 6 = x) : bla 3 = x := by
  fail_if_success simp
  fail_if_success simp only
  simp [bla]
  guard_target =ₛ 6 = x
  assumption

example (h : 6 = x) : bla 3 = x := by
  fail_if_success simp
  fail_if_success simp only
  simp [bla]
  guard_target =ₛ 6 = x
  assumption

example (h : 6 = x) : bla 3 = x := by
  simp only [bla]
  guard_target =ₛ 2*3 = x
  assumption

example (h : 6 = x) : bla 3 = x := by
  simp only [bla, Nat.reduceMul]
  guard_target =ₛ 6 = x
  assumption

attribute [simp] reduceBla

example (h : 6 = x) : bla 3 = x := by
  simp
  guard_target =ₛ 6 = x
  assumption

example (h : 5 = x) : 2 + 3 = x := by
  dsimp
  guard_target =ₛ 5 = x
  assumption
