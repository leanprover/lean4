import Std.Sync.SharedMutex

def countIt (mutex : Std.SharedMutex Nat) : IO Unit := do
  for _ in [0:1000] do
    mutex.atomically do
      modify fun s => s + 1

def atomically : IO Unit := do
  let mutex ← Std.SharedMutex.new 0
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

def holdIt (mutex : Std.SharedMutex Nat) (ref : IO.Ref Nat) : IO Unit := do
  mutex.atomically do
    ref.set 1
    modify fun s => s + 1
    while (← ref.get) == 1 do
      IO.sleep 1

def tryIt (mutex : Std.SharedMutex Nat) (ref : IO.Ref Nat) : IO Unit := do
  while (← ref.get) == 0 do
    IO.sleep 1
  let success ← mutex.tryAtomically (modify fun s => s + 1)
  if success.isSome then throw <| .userError s!"lock succeeded but shouldn't"
  ref.set 2
  mutex.atomically (modify fun s => s + 1)
  let success ← mutex.tryAtomically (modify fun s => s + 1)
  if success.isNone then throw <| .userError s!"lock didn't succeed but should"


def tryAtomically : IO Unit := do
  let mutex ← Std.SharedMutex.new 0
  let ref ← IO.mkRef 0
  let t1 ← IO.asTask (prio := .dedicated) (holdIt mutex ref)
  let t2 ← IO.asTask (prio := .dedicated) (tryIt mutex ref)
  IO.ofExcept t1.get
  IO.ofExcept t2.get
  mutex.atomically do
    let val ← get
    if val != 3 then
      throw <| .userError s!"Should be 3 but was {val}"

def readIt (mutex : Std.SharedMutex Nat) : IO Unit := do
  mutex.atomicallyRead do
    let val ← read
    if val != 37 then
      throw <| .userError s!"Value should be 37 but was {val}"

def atomicallyRead : IO Unit := do
  let mutex ← Std.SharedMutex.new 37
  let t1 ← IO.asTask (prio := .dedicated) (readIt mutex)
  let t2 ← IO.asTask (prio := .dedicated) (readIt mutex)
  IO.ofExcept t1.get
  IO.ofExcept t2.get

def tryWriteIt (mutex : Std.SharedMutex Nat) (ref : IO.Ref Nat) : IO Unit := do
  let success ←
    mutex.tryAtomically do
      ref.set 1
      modify fun s => s + 1
      while (← ref.get) == 1 do
        IO.sleep 1
  if success.isNone then throw <| .userError s!"write lock failed"

def tryReadIt (mutex : Std.SharedMutex Nat) (ref : IO.Ref Nat) : IO Unit := do
  while (← ref.get) == 0 do
    IO.sleep 1
  let success ← mutex.tryAtomically (modify fun s => s + 1)
  if success.isSome then throw <| .userError s!"write lock succeeded but shouldn't"
  let success ← mutex.tryAtomicallyRead read
  if success.isSome then throw <| .userError s!"read lock succeeded but shouldn't"
  ref.set 2
  let val ← mutex.atomicallyRead read
  if val != 1 then throw <| .userError s!"value should be 1 but was {val}"
  mutex.atomicallyRead do
    ref.set 3
    while (← ref.get) == 3 do
      IO.sleep 1

def tryReadIt' (mutex : Std.SharedMutex Nat) (ref : IO.Ref Nat) : IO Unit := do
  while (← ref.get) != 3 do
    IO.sleep 1
  let val ← mutex.tryAtomicallyRead read
  if val != some 1 then throw <| .userError s!"value should be `some 1` but was {val}"
  ref.set 4

def tryAtomicallyRead : IO Unit := do
  let mutex ← Std.SharedMutex.new 0
  let ref ← IO.mkRef 0
  let t1 ← IO.asTask (prio := .dedicated) (tryWriteIt mutex ref)
  let t2 ← IO.asTask (prio := .dedicated) (tryReadIt mutex ref)
  let t3 ← IO.asTask (prio := .dedicated) (tryReadIt' mutex ref)
  IO.ofExcept t1.get
  IO.ofExcept t2.get
  IO.ofExcept t3.get
  mutex.atomically do
    let val ← get
    if val != 1 then
      throw <| .userError s!"Should be 1 but was {val}"

#eval atomically
#eval atomicallyRead
#eval tryAtomically
#eval tryAtomicallyRead
