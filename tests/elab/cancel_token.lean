/-! Tests for `IO.CancelToken.onSet` and `IO.CancelToken.task`. -/

/-- `onSet` registered before `set` fires synchronously when `set` is called. -/
def testOnSetBeforeSet : IO Unit := do
  let tk ← IO.CancelToken.new
  let cell ← IO.mkRef false
  tk.onSet (cell.set true)
  if (← cell.get) then panic! "onSet fired too early"
  tk.set
  if !(← cell.get) then panic! "onSet did not fire"
  IO.println "ok"

/-- `onSet` registered after `set` fires immediately at registration time. -/
def testOnSetAfterSet : IO Unit := do
  let tk ← IO.CancelToken.new
  tk.set
  let cell ← IO.mkRef false
  tk.onSet (cell.set true)
  if !(← cell.get) then panic! "onSet did not fire on already-set token"
  IO.println "ok"

/-- Multiple `onSet` callbacks all fire. -/
def testOnSetMultiple : IO Unit := do
  let tk ← IO.CancelToken.new
  let counter ← IO.mkRef 0
  for _ in [0:5] do
    tk.onSet (counter.modify (· + 1))
  tk.set
  let n ← counter.get
  if n != 5 then panic! s!"expected 5 callbacks, got {n}"
  IO.println "ok"

/-- `task` returns a task that resolves once the token is set, with `some ()`. -/
def testTask : IO Unit := do
  let tk ← IO.CancelToken.new
  let t := tk.task
  tk.set
  match t.get with
  | some () => IO.println "ok"
  | none    => panic! "task fired with none after set"

/-- `task` resolves to `none` when the token is dropped without being set. -/
def testTaskDropped : IO Unit := do
  let t ← do
    let tk ← IO.CancelToken.new
    pure tk.task
  -- `tk` is now out of scope; the underlying promise is dropped.
  match t.get with
  | none    => IO.println "ok"
  | some () => panic! "task fired with some on dropped token"

/--
info: ok
ok
ok
ok
ok
-/
#guard_msgs in
#eval do
  testOnSetBeforeSet
  testOnSetAfterSet
  testOnSetMultiple
  testTask
  testTaskDropped
