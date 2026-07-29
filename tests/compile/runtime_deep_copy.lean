/-!
Tests for `Runtime.deepCopy`. Copies of scalars, constructors (including scalar fields),
arrays, scalar arrays, strings, and big numbers must compare equal to the originals;
the copy must not share allocations with the input but must preserve sharing within
the copied graph; closures, thunks, tasks, refs, promises, and external objects are
rejected, including when nested inside otherwise copyable data.
-/

structure S where
  name : String
  data : Array Nat
  byte : UInt8
  flag : Bool
  flt  : Float
  big  : Nat
  deriving BEq

def check [BEq α] (tag : String) (a : α) : IO Unit := do
  let b ← Runtime.deepCopy a
  unless a == b do throw <| IO.userError s!"{tag}: copy differs from original"
  IO.println s!"{tag}: ok"

def expectError (tag : String) (act : IO Unit) : IO Unit := do
  match ← act.toBaseIO with
  | .ok _    => IO.println s!"{tag}: no error!"
  | .error e => IO.println s!"{tag}: {e}"

set_option compiler.extract_closed false in
unsafe def main : IO UInt32 := do
  -- scalars
  check "small Nat" (5 : Nat)
  check "neg Int" (-7 : Int)
  -- constructors with only scalar fields
  check "Char" 'λ'
  check "Float" (3.25 : Float)
  check "UInt64" (0xc0ffee : UInt64)
  -- big numbers
  check "big Nat" ((2 : Nat) ^ 100)
  check "big Int" (-(2 : Int) ^ 100)
  -- strings
  check "String" "hello λ world"
  check "empty String" ""
  -- arrays
  check "Array" (#[1, 2, 3] : Array Nat)
  check "empty Array" (#[] : Array Nat)
  check "nested Array" (#[#["a"], #["b", "c"]] : Array (Array String))
  -- scalar arrays
  check "ByteArray" "scalar data".toUTF8
  check "FloatArray" <| FloatArray.mk #[1.5, 2.5, 3.5]
  -- inductives and structures
  check "List" (List.range 10)
  check "Option" (some "x")
  check "structure" ({ name := "s", data := #[1, 2], byte := 42, flag := true,
                       flt := 2.5, big := 2 ^ 80 } : S)
  -- a long list must not overflow the C stack
  check "long list" (List.range 500_000)
  -- the copy is fresh, but sharing inside the input is preserved
  let s := String.ofList "abc".toList
  let p := (s, s)
  let p' ← Runtime.deepCopy p
  if ptrEq p'.1 s then throw <| IO.userError "sharing: copy shares allocation with input"
  unless ptrEq p'.1 p'.2 do throw <| IO.userError "sharing: not preserved"
  IO.println "sharing: ok"
  -- non-copyable objects
  expectError "closure" do discard <| Runtime.deepCopy fun (_ : Nat) => 1
  expectError "thunk" do discard <| Runtime.deepCopy (Thunk.mk fun _ => 1)
  expectError "task" do discard <| Runtime.deepCopy (Task.spawn fun _ => 1)
  expectError "ref" do discard <| Runtime.deepCopy (← IO.mkRef 0)
  expectError "promise" do discard <| Runtime.deepCopy (← IO.Promise.new (α := Nat))
  expectError "external" do
    discard <| Runtime.deepCopy (← IO.FS.Handle.mk "runtime_deep_copy.lean" .read)
  expectError "nested closure" do
    discard <| Runtime.deepCopy ("abc", #[1, 2, 3], fun (_ : Nat) => 1)
  return 0
