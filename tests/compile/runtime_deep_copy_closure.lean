/-!
Tests closures in `Runtime.deepCopy`.
Separate from `runtime_deep_copy` because it must be compiled
(closures produced by the interpreter cannot be copied).
-/

def check (tag : String) (f : Nat → Nat) : IO Unit := do
  let g ← Runtime.deepCopy f
  unless f 42 == g 42 do
    throw <| IO.userError s!"{tag}: copy differs from original given 42 as input"
  IO.println s!"{tag}: ok"

def expectError (tag : String) (act : IO Unit) : IO Unit := do
  match ← act.toBaseIO with
  | .ok _    => IO.println s!"{tag}: no error!"
  | .error e => IO.println s!"{tag}: {e}"

set_option compiler.extract_closed false in
unsafe def main : IO UInt32 := do
  -- closure that captures nothing
  check "empty closure" fun (n : Nat) => n
  let k : Nat ← IO.rand 13 37
  -- capture a local scalar
  check "scalar closure" fun (n : Nat) => n + k
  -- use a Task in the implementation
  check "closure using Task" fun (n : Nat) =>
    let t := Task.spawn fun _ => n
    t.get
  -- capture a Ref
  let r ← IO.mkRef 4
  expectError "nested ref" do discard <| Runtime.deepCopy fun (_ : Nat) => r.get (m := IO)
  return 0
