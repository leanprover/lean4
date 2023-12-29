import Lean.Meta.Tactic.Simp.Simproc
import Lean.Meta.Offset

def foo (x : Nat) : Nat :=
  x + 10

simproc reduce_f (foo _) := fun e => open Lean Meta in do
  let some n ← evalNat e.appArg! |>.run | return none
  return some (.done { expr := mkNatLit (n+10) })

example : x + foo 2 = 12 + x := by
  fail_if_success simp (config := { «simproc» := false })
  simp (config := { «simproc» := true })
  rw [Nat.add_comm]
