import Std.Sync.Mutex

def countIt (mutex : Std.Mutex Nat) : IO Unit := do
  for _ in [0:1000] do
    mutex.atomically do
      modify fun s => s + 1

def atomically : IO Unit := do
  let mutex ← Std.Mutex.new 0
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

def holdIt (mutex : Std.Mutex Nat) (ref : IO.Ref Nat) : IO Unit := do
  mutex.atomically do
    ref.set 1
    modify fun s => s + 1
    while (← ref.get) == 1 do
      IO.sleep 1

def tryIt (mutex : Std.Mutex Nat) (ref : IO.Ref Nat) : IO Unit := do
  while (← ref.get) == 0 do
    IO.sleep 1
  let success ← mutex.tryAtomically (modify fun s => s + 1)
  if success.isSome then throw <| .userError s!"lock succeeded but shouldn't"
  ref.set 2
  mutex.atomically (modify fun s => s + 1)
  let success ← mutex.tryAtomically (modify fun s => s + 1)
  if success.isNone then throw <| .userError s!"lock didn't succeed but should"


def tryAtomically : IO Unit := do
  let mutex ← Std.Mutex.new 0
  let ref ← IO.mkRef 0
  let t1 ← IO.asTask (prio := .dedicated) (holdIt mutex ref)
  let t2 ← IO.asTask (prio := .dedicated) (tryIt mutex ref)
  IO.ofExcept t1.get
  IO.ofExcept t2.get
  mutex.atomically do
    let val ← get
    if val != 3 then
      throw <| .userError s!"Should be 3 but was {val}"

def workIt (mutex : Std.Mutex Nat) (cond : Std.Condvar) : IO Unit := do
  for _ in [0:1000] do
    mutex.atomically do (modify fun s => s + 1)
    cond.notifyAll

def finishIt (mutex : Std.Mutex Nat) (cond : Std.Condvar) : IO Unit := do
  mutex.atomicallyOnce cond (do return (← get) == 1000) do
    modify fun s => s + 41000


def condVar : IO Unit := do
  let mutex ← Std.Mutex.new 0
  let cond ← Std.Condvar.new
  let t1 ← IO.asTask (prio := .dedicated) (workIt mutex cond)
  let t2 ← IO.asTask (prio := .dedicated) (finishIt mutex cond)
  IO.ofExcept t1.get
  IO.ofExcept t2.get
  mutex.atomically do
    let val ← get
    if val != 42000 then
      throw <| .userError s!"Should be 42000 but was {val}"

#eval atomically
#eval tryAtomically
#eval condVar
