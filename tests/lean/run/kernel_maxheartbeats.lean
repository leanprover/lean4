import Lean

def ack : Nat → Nat → Nat
  | 0,   y   => y+1
  | x+1, 0   => ack x 1
  | x+1, y+1 => ack x (ack (x+1) y)

set_option maxHeartbeats 500
open Lean Meta

/--
error: (kernel) deterministic timeout
-/
#guard_msgs in
run_meta do
  let type ← mkEq (← mkAppM ``ack #[mkNatLit 4, mkNatLit 4]) (mkNatLit 100000)
  let value ← mkEqRefl (mkNatLit 100000)
  addDecl <| .thmDecl {
    name        := `ack_4_4
    levelParams := []
    type, value
  }
