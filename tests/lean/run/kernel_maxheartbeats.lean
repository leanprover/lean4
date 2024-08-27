import Lean

noncomputable def ack' (a : Nat × Nat) : Nat :=
  let wf : WellFoundedRelation (Nat × Nat) := by exact Prod.instWellFoundedRelation
  WellFounded.fixF
  (fun p ih => match p with
  | (0,   y)   => y+1
  | (x+1, 0)   => ih (x, 1) (by decreasing_tactic)
  | (x+1, y+1) => ih (x, ih (x+1, y) (by decreasing_tactic)) (by decreasing_tactic)
  )
  a
  (wf.2.apply a)

noncomputable def ack : Nat → Nat → Nat := fun a b => ack' (a,b)

set_option maxHeartbeats 500
open Lean Meta

/-- error: (kernel) deterministic timeout -/
#guard_msgs in
run_meta do
  let type ← mkEq (← mkAppM ``ack #[mkNatLit 4, mkNatLit 4]) (mkNatLit 100000)
  let value ← mkEqRefl (mkNatLit 100000)
  addDecl <| .thmDecl {
    name        := `ack_4_4
    levelParams := []
    type, value
  }
