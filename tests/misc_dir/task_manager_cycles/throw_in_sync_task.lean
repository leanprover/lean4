module

/-!
An exception that the interpreter raises in a nested `(sync := true)` task, here for a missing native
implementation, makes `lean --run` fail instead of hanging at exit.
-/

@[extern "lean_test_no_such_native_symbol"]
opaque missing (n : Nat) : BaseIO Nat

public def main : IO Unit := do
  let p ← IO.Promise.new (α := Nat)
  let t := p.result?.map (sync := true) (·.getD 0)
  BaseIO.chainTask (sync := true) t fun v => discard <| missing v
  p.resolve 1
