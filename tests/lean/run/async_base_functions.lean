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
  discard <| Async.concurrently (wait 200 ref 1) (wait 1000 ref 2)
  ref.atomically (·.modify (· * 10))
  assert! (← ref.atomically (·.get)) == 30

#eval do (← conc.toEIO).block

def racer : Async Unit := do
  let ref ← Std.Mutex.new 0
  Async.race (wait 200 ref 1) (wait 1000 ref 2)
  ref.atomically (·.modify (· * 10))
  assert! (← ref.atomically (·.get)) == 10

#eval do (← racer.toEIO).block

def concAll : Async Unit := do
  let ref ← Std.Mutex.new 0
  discard <| Async.concurrentlyAll #[(wait 200 ref 1), (wait 1000 ref 2)]
  ref.atomically (·.modify (· * 10))
  assert! (← ref.atomically (·.get)) == 30

#eval do (← concAll.toEIO).block

def racerAll : Async Unit := do
  let ref ← Std.Mutex.new 0
  Async.raceAll #[(wait 200 ref 1), (wait 1000 ref 2)]
  ref.atomically (·.modify (· * 10))
  assert! (← ref.atomically (·.get)) == 10

#eval do (← racerAll.toEIO).block

def racerAllNotCancels : Async Unit := do
  let ref ← Std.Mutex.new 0
  Async.raceAll #[(wait 200 ref 1), (wait 700 ref 2)]
  ref.atomically (·.modify (· * 10))
  IO.sleep 1000
  assert! (← ref.atomically (·.get)) == 12

#eval do (← racerAllNotCancels.toEIO).block

def racerAllError : Async Unit := do
  let ref ← Std.Mutex.new 0
  Async.raceAll #[(wait 400 ref 2), throw (IO.userError "error wins")]

/-- error: error wins -/
#guard_msgs in
#eval do (← racerAllError.toEIO).block

def racerAllErrorLost : Async Unit := do
  let result ← Async.raceAll #[(do IO.sleep 1000; throw (IO.userError "error wins")) , (do IO.sleep 200; pure 10)]
  assert! result = 10

#eval do (← racerAllErrorLost.toEIO).block
