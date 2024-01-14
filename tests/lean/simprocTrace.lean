import Lean.Meta.Tactic.Simp.Simproc
import Lean.Meta.Offset

def foo (x : Nat) : Nat :=
  x + 10

simproc reduce_foo (foo _) := fun e => open Lean Meta in do
  let some n ← evalNat e.appArg! |>.run | return none
  return some (.done { expr := mkNatLit (n+10) })

set_option tactic.simp.trace true
example : x + foo 2 = 12 + x := by
  simp
  rw [Nat.add_comm]
