import Std.Sync

open Std

def assertBEq [BEq α] [ToString α] (is should : α) : IO Unit := do
  if is != should then
    throw <| .userError s!"{is} should be {should}"

def resolveOnce (f : Future Nat) : IO Unit := do
  assertBEq (← f.isResolved) false
  assertBEq (← f.tryGet) none
  assertBEq (← f.resolve 42) true
  assertBEq (← f.isResolved) true
  assertBEq (← f.tryGet) (some 42)
  assertBEq (← f.resolve 43) false
  assertBEq (← f.tryGet) (some 42)

def getAfterResolve (f : Future Nat) : IO Unit := do
  assertBEq (← f.resolve 37) true
  let task ← f.get
  assertBEq (← IO.wait task) 37

def getBeforeResolve (f : Future Nat) : IO Unit := do
  let task ← f.get
  assertBEq (← f.resolve 37) true
  assertBEq (← IO.wait task) 37

def multipleGets (f : Future Nat) : IO Unit := do
  let task1 ← f.get
  let task2 ← f.get
  let task3 ← f.get
  assertBEq (← f.resolve 99) true
  assertBEq (← IO.wait task1) 99
  assertBEq (← IO.wait task2) 99
  assertBEq (← IO.wait task3) 99

def concurrentResolve (f : Future Nat) : IO Unit := do
  let resolveTask1 ← IO.asTask (f.resolve 10)
  let resolveTask2 ← IO.asTask (f.resolve 20)
  let resolveTask3 ← IO.asTask (f.resolve 30)

  let result1 ← IO.ofExcept =<< IO.wait resolveTask1
  let result2 ← IO.ofExcept =<< IO.wait resolveTask2
  let result3 ← IO.ofExcept =<< IO.wait resolveTask3

  let successCount := [result1, result2, result3].filter id |>.length
  assertBEq successCount 1

  let value ← f.tryGet
  assertBEq (value.isSome) true
  assertBEq ([10, 20, 30].contains value.get!) true

def concurrentGetResolve (f : Future Nat) : IO Unit := do
  let getTask1 ← f.get
  let getTask2 ← f.get
  let resolveTask ← f.resolve 55
  let getTask3 ← f.get

  let value1 ← IO.wait getTask1
  let value2 ← IO.wait getTask2
  let value3 ← IO.wait getTask3

  assertBEq resolveTask true
  assertBEq value1 55
  assertBEq value2 55
  assertBEq value3 55

def suite : IO Unit := do
  resolveOnce (← Future.new)
  getAfterResolve (← Future.new)
  getBeforeResolve (← Future.new)
  multipleGets (← Future.new)
  concurrentResolve (← Future.new)
  concurrentGetResolve (← Future.new)

#eval suite
