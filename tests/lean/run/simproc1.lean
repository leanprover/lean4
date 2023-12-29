import Lean.Meta.Tactic.Simp.Simproc
import Lean.Meta.Offset

def foo (x : Nat) : Nat :=
  x + 10

simproc reduce_foo (foo _) := fun e => open Lean Meta in do
  let some n ← evalNat e.appArg! |>.run | return none
  return some (.done { expr := mkNatLit (n+10) })

example : x + foo 2 = 12 + x := by
  fail_if_success simp (config := { «simproc» := false })
  simp (config := { «simproc» := true })
  rw [Nat.add_comm]

example : x + foo 2 = 12 + x := by
  -- `simp only` must not use the default simproc set
  fail_if_success simp (config := { «simproc» := true }) only
  simp (config := { «simproc» := true })
  rw [Nat.add_comm]

example : x + foo 2 = 12 + x := by
  -- `simp only` does not use the default simproc set, but we can provide simprocs as arguments
  simp (config := { «simproc» := true }) only [reduce_foo]
  rw [Nat.add_comm]
