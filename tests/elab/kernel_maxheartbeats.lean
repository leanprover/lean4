import Lean

def fib : Nat → Nat
  | 0     => 0
  | 1     => 1
  | n + 2 => fib (n + 1) + fib n

set_option maxHeartbeats 500
open Lean Meta

/-- error: (kernel) deterministic timeout -/
#guard_msgs in
run_meta do
  let type ← mkEq (← mkAppM ``fib #[mkNatLit 10000]) (mkNatLit 100000)
  let value ← mkEqRefl (mkNatLit 100000)
  addDecl <| .thmDecl {
    name        := `ack_4_4
    levelParams := []
    type, value
  }
