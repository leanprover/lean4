import Lean

/-!
Looking up an imported constant costs the same heartbeats whether or not it hits the shared lookup
cache, so that heartbeat counts do not depend on which thread looked up a name first.
-/

open Lean

@[noinline] def lookup (env : Environment) (n : Name) : Bool :=
  (env.find? n).isSome

def lookupHeartbeats (env : Environment) (n : Name) : IO Nat := do
  let h₀ ← IO.getNumHeartbeats
  let found := lookup env n
  -- checks the result before reading the heartbeats again, so that the lookup is not moved past it
  unless found do throw <| IO.userError s!"{n} not found"
  let h₁ ← IO.getNumHeartbeats
  return h₁ - h₀

/-- info: true -/
#guard_msgs in
#eval show CoreM _ from do
  let env ← getEnv
  -- a name that elaborating this file does not look up otherwise
  let n := `Lean.IR.EmitLLVM.emitMainFn
  -- the first call of the functions above allocates in the interpreter
  discard <| lookupHeartbeats env `Lean.IR.EmitLLVM.emitFnDecls
  let miss ← lookupHeartbeats env n
  let hit ← lookupHeartbeats env n
  return miss == hit
