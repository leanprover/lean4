import Lean

/-!
Tests that the kernel `maxHeartbeats` limit of `addDeclCore` applies to each declaration separately
instead of accumulating over all declarations checked on the same thread.
-/

open Lean

def decl (i : Nat) : Declaration :=
  .defnDecl { name := .num `c i, levelParams := [], type := .sort 2, value := .sort 1,
              hints := .opaque, safety := .safe }

/-- Adds declarations `0, ..., n - 1` with a kernel limit of 100 heartbeats each. -/
def addAll (env : Kernel.Environment) (n : Nat) : IO Unit := do
  let mut env := env
  for i in [0:n] do
    match env.addDeclCore 100 0 (decl i) none with
    | .ok env' => env := env'
    | .error e => throw <| .userError s!"c.{i} failed: {← (e.toMessageData {}).toString}"
  IO.println s!"all {n} accepted"

/-- info: all 1000 accepted -/
#guard_msgs in
#eval show IO Unit from do
  addAll (← mkEmptyEnvironment).toKernelEnv 1000

/-! The limit still applies within a single declaration. -/

def fib : Nat → Nat
  | 0     => 0
  | 1     => 1
  | n + 2 => fib (n + 1) + fib n

/-- info: (kernel) deterministic timeout -/
#guard_msgs in
open Meta in
run_meta do
  let type ← mkEq (← mkAppM ``fib #[mkNatLit 10000]) (mkNatLit 100000)
  let value ← mkEqRefl (mkNatLit 100000)
  let decl := .thmDecl { name := `fibEq, levelParams := [], type, value }
  match (← getEnv).toKernelEnv.addDeclCore 500 0 decl none with
  | .ok _ => logInfo "accepted"
  | .error e => logInfo (e.toMessageData {})
