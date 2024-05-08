import Lean.Elab.ElabRules

open Lean

elab "file_pos%" : term => return toExpr <| (← getFileMap).toPosition (← getRefPos)

def assertBEq
  [BEq α] [ToString α] (actual expected : α)
  (filePos : Position := by exact file_pos%)
: IO Unit :=
  unless actual == expected do
    throw <| IO.userError <| s!"assert[{filePos.line}:{filePos.column}]: \
      expected '{expected}', got '{actual}'"

def test : IO Unit := do
  let p1 : IO.Promise Unit ← IO.Promise.new -- resolving queues the task
  let p2 : IO.Promise Unit ← IO.Promise.new -- resolved once task is running
  let p3 : IO.Promise Unit ← IO.Promise.new -- resolving finishes the task
  let t ← BaseIO.mapTask (fun () => do p2.resolve (); IO.wait p3.result) p1.result
  assertBEq (← IO.getTaskState p1.result) .running
  assertBEq (← IO.getTaskState p2.result) .running
  assertBEq (← IO.getTaskState p3.result) .running
  assertBEq (← IO.getTaskState t) .waiting
  p1.resolve ()
  assertBEq (← IO.getTaskState p1.result) .finished
  IO.wait p2.result
  assertBEq (← IO.getTaskState p2.result) .finished
  assertBEq (← IO.getTaskState t) .running
  p3.resolve ()
  assertBEq (← IO.getTaskState p3.result) .finished
  IO.wait t
  assertBEq (← IO.getTaskState t) .finished

#eval test
