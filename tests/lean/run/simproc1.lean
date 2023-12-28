import Lean.Meta.Tactic.Simp.Simproc
import Lean.Meta.Offset

def foo (x : Nat) : Nat :=
  x + 10

open Lean Meta Simp
@[simproc foo _]
def simp_f : Simproc := fun e => do
  let some n ← evalNat e.appArg! |>.run
    | return none
  return some (.done { expr := mkNatLit (n+10) })

example : x + foo 2 = 12 + x := by
  fail_if_success simp (config := { simproc := false })
  simp (config := { simproc := true })
  rw [Nat.add_comm]
