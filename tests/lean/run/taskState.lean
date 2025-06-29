def assertBEq [BEq α] [ToString α] (caption : String) (actual expected : α) : IO Unit := do
  unless actual == expected do
    throw <| IO.userError <|
      s!"{caption}: expected '{expected}', got '{actual}'"

def test : IO Unit := do
  let p1 : IO.Promise Unit ← IO.Promise.new -- resolving queues the task
  let p2 : IO.Promise Unit ← IO.Promise.new -- resolved once task is running
  let p3 : IO.Promise Unit ← IO.Promise.new -- resolving finishes the task
  let t ← BaseIO.mapTask (fun _ => do p2.resolve (); IO.wait p3.result?) p1.result?
  assertBEq "p1" (← IO.getTaskState p1.result?) .running
  assertBEq "p2" (← IO.getTaskState p2.result?) .running
  assertBEq "p3" (← IO.getTaskState p3.result?) .running
  assertBEq "t" (← IO.getTaskState t) .waiting
  p1.resolve ()
  assertBEq "p1" (← IO.getTaskState p1.result?) .finished
  let _ ← IO.wait p2.result?
  assertBEq "p2" (← IO.getTaskState p2.result?) .finished
  assertBEq "t" (← IO.getTaskState t) .running
  p3.resolve ()
  assertBEq "p3" (← IO.getTaskState p3.result?) .finished
  let _ ← IO.wait t
  assertBEq "t" (← IO.getTaskState t) .finished

#eval test
