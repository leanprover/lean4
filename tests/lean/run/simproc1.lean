import Lean.Meta.Tactic.Simp.Simproc
import Lean.Meta.Offset

def foo (x : Nat) : Nat :=
  x + 10

simproc reduce_foo (foo _) := fun e => open Lean Meta in do
  let some n ← evalNat e.appArg! |>.run | return none
  return some (.done { expr := mkNatLit (n+10) })

example : x + foo 2 = 12 + x := by
  set_option simprocs false in
    fail_if_success simp
  simp
  rw [Nat.add_comm]

example : x + foo 2 = 12 + x := by
  -- `simp only` must not use the default simproc set
  fail_if_success simp only
  simp
  rw [Nat.add_comm]

example : x + foo 2 = 12 + x := by
  -- `simp only` does not use the default simproc set, but we can provide simprocs as arguments
  simp only [reduce_foo]
  rw [Nat.add_comm]
