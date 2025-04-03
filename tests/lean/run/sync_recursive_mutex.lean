import Std.Sync.RecursiveMutex

def countIt (mutex : Std.RecursiveMutex Nat) : IO Unit := do
  for _ in [0:1000] do
    mutex.atomically do
      modify fun s => s + 1

def atomically : IO Unit := do
  let mutex ← Std.RecursiveMutex.new 0
  let t1 ← IO.asTask (prio := .dedicated) (countIt mutex)
  let t2 ← IO.asTask (prio := .dedicated) (countIt mutex)
  let t3 ← IO.asTask (prio := .dedicated) (countIt mutex)
  let t4 ← IO.asTask (prio := .dedicated) (countIt mutex)
  IO.ofExcept t1.get
  IO.ofExcept t2.get
  IO.ofExcept t3.get
  IO.ofExcept t4.get
  mutex.atomically do
    let val ← get
    if val != 4000 then
      throw <| .userError s!"Should be 4000 but was {val}"

def holdIt (mutex : Std.RecursiveMutex Nat) (ref : IO.Ref Nat) : IO Unit := do
  mutex.atomically do
    ref.set 1
    modify fun s => s + 1
    while (← ref.get) == 1 do
      IO.sleep 1

def tryIt (mutex : Std.RecursiveMutex Nat) (ref : IO.Ref Nat) : IO Unit := do
  while (← ref.get) == 0 do
    IO.sleep 1
  let success ← mutex.tryAtomically (modify fun s => s + 1)
  if success.isSome then throw <| .userError s!"lock succeeded but shouldn't"
  ref.set 2
  mutex.atomically (modify fun s => s + 1)
  let success ← mutex.tryAtomically (modify fun s => s + 1)
  if success.isNone then throw <| .userError s!"lock didn't succeed but should"


def tryAtomically : IO Unit := do
  let mutex ← Std.RecursiveMutex.new 0
  let ref ← IO.mkRef 0
  let t1 ← IO.asTask (prio := .dedicated) (holdIt mutex ref)
  let t2 ← IO.asTask (prio := .dedicated) (tryIt mutex ref)
  IO.ofExcept t1.get
  IO.ofExcept t2.get
  mutex.atomically do
    let val ← get
    if val != 3 then
      throw <| .userError s!"Should be 3 but was {val}"

def recursive : IO Unit := do
  let mutex ← Std.RecursiveMutex.new 0
  mutex.atomically do
    mutex.atomically do
      modify fun s => s + 1

  mutex.atomically do
    discard <| mutex.tryAtomically do
      modify fun s => s + 1

  mutex.atomically do
    let val ← get
    if val != 2 then
      throw <| .userError s!"Should be 2 but was {val}"

#eval atomically
#eval tryAtomically
#eval recursive
