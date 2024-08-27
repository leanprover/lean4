import Lean

def fib (n : Nat) :=
  match n with
  | 0 | 1 => 1
  | x+2 => fib x + fib (x+1)
termination_by structural n

set_option maxHeartbeats 100
open Lean Meta

/--
error: (deterministic) timeout at `elaborator`, maximum number of heartbeats (100) has been reached
Use `set_option maxHeartbeats <num>` to set the limit.
Additional diagnostic information may be available using the `set_option diagnostics true` command.
---
error: (deterministic) timeout at `isDefEq`, maximum number of heartbeats (100) has been reached
Use `set_option maxHeartbeats <num>` to set the limit.
Additional diagnostic information may be available using the `set_option diagnostics true` command.
---
error: (deterministic) timeout at `isDefEq`, maximum number of heartbeats (100) has been reached
Use `set_option maxHeartbeats <num>` to set the limit.
Additional diagnostic information may be available using the `set_option diagnostics true` command.
---
error: (deterministic) timeout at `whnf`, maximum number of heartbeats (100) has been reached
Use `set_option maxHeartbeats <num>` to set the limit.
Additional diagnostic information may be available using the `set_option diagnostics true` command.
---
error: (deterministic) timeout at `isDefEq`, maximum number of heartbeats (100) has been reached
Use `set_option maxHeartbeats <num>` to set the limit.
Additional diagnostic information may be available using the `set_option diagnostics true` command.
---
error: (deterministic) timeout at `whnf`, maximum number of heartbeats (100) has been reached
Use `set_option maxHeartbeats <num>` to set the limit.
Additional diagnostic information may be available using the `set_option diagnostics true` command.
---
error: (deterministic) timeout at `isDefEq`, maximum number of heartbeats (100) has been reached
Use `set_option maxHeartbeats <num>` to set the limit.
Additional diagnostic information may be available using the `set_option diagnostics true` command.
---
error: (deterministic) timeout at `isDefEq`, maximum number of heartbeats (100) has been reached
Use `set_option maxHeartbeats <num>` to set the limit.
Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
run_meta do
  let type ← mkEq (← mkAppM ``fib #[mkNatLit 200]) (mkNatLit 453973694165307953197296969697410619233826)
  let value ← mkEqRefl (mkNatLit 453973694165307953197296969697410619233826)
  addDecl <| .thmDecl {
    name        := `fib_30
    levelParams := []
    type, value
  }
