import Std.Internal.Async
import Std.Sync.Mutex

open Std

open Std.Internal.IO.Async

def wait (ms : UInt32) (ref : Std.Mutex Nat) (val : Nat) : Async Unit := do
  ref.atomically (·.modify (· * val))
  IO.sleep ms
  ref.atomically (·.modify (· + val))

-- Tests

def sequential : Async Unit := do
  let ref ← Std.Mutex.new 0
  wait 200 ref 1
  wait 400 ref 2
  ref.atomically (·.modify (· * 10))
  assert! (← ref.atomically (·.get)) == 40

#eval do (← sequential.toEIO).block

def conc : Async Unit := do
  let ref ← Std.Mutex.new 0
  discard <| concurrently (wait 200 ref 1) (wait 400 ref 2)
  ref.atomically (·.modify (· * 10))
  assert! (← ref.atomically (·.get)) == 30

#eval do (← conc.toEIO).block

def racer : Async Unit := do
  let ref ← Std.Mutex.new 0
  race (wait 200 ref 1) (wait 400 ref 2)
  ref.atomically (·.modify (· * 10))
  assert! (← ref.atomically (·.get)) == 10

#eval do (← racer.toEIO).block

def concAll : Async Unit := do
  let ref ← Std.Mutex.new 0
  discard <| concurrentlyAll #[(wait 200 ref 1), (wait 400 ref 2)]
  ref.atomically (·.modify (· * 10))
  assert! (← ref.atomically (·.get)) == 30

#eval do (← concAll.toEIO).block

def racerAll : Async Unit := do
  let ref ← Std.Mutex.new 0
  raceAll #[(wait 200 ref 1), (wait 400 ref 2)]
  ref.atomically (·.modify (· * 10))
  assert! (← ref.atomically (·.get)) == 10

#eval do (← racerAll.toEIO).block
