import Lean

@[seval] def f (x : Nat) := x + 2

example (h : y = 2) : f x = x + y := by
  fail_if_success simp
  simp only [seval, h]

def g (x : Nat) := x + x

@[seval] theorem g_eq : g x = 2 * x := by
  simp +arith [g]

example (h : y = 2) : g x + 2 = 2 * x + y := by
  fail_if_success simp
  simp only [seval, h]

def boo (x : Nat) : Nat :=
  x + 10

open Lean Meta in
simproc [seval] reduceBoo (boo _) := fun e => do
  unless e.isAppOfArity ``boo 1 do return .continue
  let some n ← Nat.fromExpr? e.appArg! | return .continue
  return .done { expr := mkNatLit (n+10) }

example : f x + boo 2 = id (x + 2) + 12 := by
  fail_if_success (simp; done)
  simp only [seval, id] -- Applies the simp and simproc sets
