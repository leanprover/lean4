/-!
Tests for `Runtime.deepCopy`. Copies of scalars, constructors (including scalar fields),
arrays, scalar arrays, strings, big numbers, evaluated thunks, finished tasks, and resolved
promises must compare equal to the originals; the copy must not share allocations with the input
but must preserve sharing within the copied graph; unevaluated thunks, unfinished tasks,
unresolved promises, refs, and external objects are rejected, including when nested inside
otherwise copyable data.
-/

structure S where
  name : String
  data : Array Nat
  byte : UInt8
  flag : Bool
  flt  : Float
  big  : Nat
  deriving BEq

/-- Checks that `a` is deep-copied to a `BEq`-equal value. -/
def check [BEq α] (tag : String) (a : α) : IO Unit := do
  let b ← Runtime.deepCopy a
  unless a == b do throw <| IO.userError s!"{tag}: copy differs from original"
  IO.println s!"{tag}: ok"

/-- Checks that `b` is `BEq`-equal to `a`, but distinct in memory.
`a` and `b` must be non-scalar. -/
unsafe def checkFresh [BEq α] (tag : String) (a b : α) : IO Unit := do
  unless a == b do throw <| IO.userError s!"{tag}: copy differs from original"
  if ptrEq a b then throw <| IO.userError s!"{tag}: copy shares allocation with input"

/-- Checks that `t` is deep-copied correctly.
`t` must already be evaluated. -/
unsafe def checkThunk [BEq α] (tag : String) (t : Thunk α) : IO Unit := do
  let t' ← Runtime.deepCopy t
  if ptrEq t t' then throw <| IO.userError s!"{tag}: copy shares allocation with input"
  checkFresh tag t.get t'.get
  IO.println s!"{tag}: ok"

/-- Checks that `t` is deep-copied correctly.
`t` must already have finished. -/
unsafe def checkTask [BEq α] (tag : String) (t : Task α) : IO Unit := do
  let t' ← Runtime.deepCopy t
  if ptrEq t t' then throw <| IO.userError s!"{tag}: copy shares allocation with input"
  unless ← IO.hasFinished t' do throw <| IO.userError s!"{tag}: copied task has not finished"
  checkFresh tag t.get t'.get
  IO.println s!"{tag}: ok"

def expectError (tag : String) (act : IO Unit) : IO Unit := do
  match ← act.toBaseIO with
  | .ok _    => IO.println s!"{tag}: no error!"
  | .error e => IO.println s!"{tag}: {e}"

@[noinline] def mkThunk (s : String) : Thunk String := Thunk.mk fun _ => s ++ "!"

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
  -- finished tasks
  checkTask "Task.pure" (Task.pure "pure")
  let t := Task.spawn fun _ => "spawned"
  discard <| IO.wait t
  checkTask "finished Task" t
  -- evaluated thunks
  checkThunk "Thunk.pure" (Thunk.pure "pure")
  let th := mkThunk "lazy"
  -- evaluate before checking
  if th.get.isEmpty then throw <| IO.userError "evaluated Thunk: unexpected value"
  checkThunk "evaluated Thunk" th
  -- the value of a task or thunk may be directly reachable, so ensure sharing
  let (t', v') ← Runtime.deepCopy (t, t.get)
  unless ptrEq t'.get v' do throw <| IO.userError "Task value sharing: not preserved"
  IO.println "Task value sharing: ok"
  let (th', v') ← Runtime.deepCopy (th, th.get)
  unless ptrEq th'.get v' do throw <| IO.userError "Thunk value sharing: not preserved"
  IO.println "Thunk value sharing: ok"
  -- resolved promises
  let p ← IO.Promise.new (α := String)
  p.resolve "resolved"
  let p' ← Runtime.deepCopy p
  if ptrEq p p' then throw <| IO.userError "Promise: copy shares allocation with input"
  if ptrEq p.result? p'.result? then throw <| IO.userError "Promise: copy shares result with input"
  unless ← p'.isResolved do throw <| IO.userError "Promise: copy is not resolved"
  checkFresh "Promise" p.result!.get p'.result!.get
  IO.println "Promise: ok"
  -- the result task of a promise may also be directly reachable (test either traversal order)
  let (p', r') ← Runtime.deepCopy (p, p.result?)
  unless ptrEq p'.result? r' do throw <| IO.userError "Promise sharing: not preserved"
  let (r', p') ← Runtime.deepCopy (p.result?, p)
  unless ptrEq p'.result? r' do throw <| IO.userError "Promise sharing: not preserved"
  IO.println "Promise sharing: ok"
  -- non-copyable objects
  expectError "unevaluated Thunk" do discard <| Runtime.deepCopy (mkThunk "never")
  -- create a forever-unfinished task via an unresolved promise
  let pending ← IO.Promise.new (α := Nat)
  expectError "unfinished Task" do discard <| Runtime.deepCopy pending.result?
  expectError "unresolved Promise" do discard <| Runtime.deepCopy pending
  expectError "Ref" do discard <| Runtime.deepCopy (← IO.mkRef 0)
  expectError "external" do
    discard <| Runtime.deepCopy (← IO.FS.Handle.mk "runtime_deep_copy.lean" .read)
  expectError "nested unfinished Task" do
    discard <| Runtime.deepCopy ("abc", #[1, 2, 3], pending.result?)
  -- ensure the Promise isn't dropped
  Runtime.hold pending
  return 0
