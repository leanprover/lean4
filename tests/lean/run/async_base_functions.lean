import Std.Internal.Async

open Std.Internal.IO.Async

def wait (ms : Nat) (ref : IO.Ref Nat) (val : Nat) : Async Unit := do
  ref.modify (· * val)
  IO.sleep ms
  ref.modify (· + val)

-- Tests

def sequential : Async Unit := do
  let ref ← IO.mkRef 0
  wait 200 ref 1
  wait 400 ref 2
  ref.modify (· * 10)
  assert! (← ref.get) == 40

#eval do (← sequential.toRawEIO).wait

def conc : Async Unit := do
  let ref ← IO.mkRef 0
  discard <| concurrently (wait 200 ref 1) (wait 400 ref 2)
  ref.modify (· * 10)
  assert! (← ref.get) == 30

#eval do (← conc.toRawEIO).wait

def racer : Async Unit := do
  let ref ← IO.mkRef 0
  race (wait 200 ref 1) (wait 400 ref 2)
  ref.modify (· * 10)
  assert! (← ref.get) == 10

#eval do (← racer.toRawEIO).wait

def concAll : Async Unit := do
  let ref ← IO.mkRef 0
  discard <| concurrentlyAll #[(wait 200 ref 1), (wait 400 ref 2)]
  ref.modify (· * 10)
  assert! (← ref.get) == 30

#eval do (← concAll.toRawEIO).wait

def racerAll : Async Unit := do
  let ref ← IO.mkRef 0
  raceAll #[(wait 200 ref 1), (wait 400 ref 2)]
  ref.modify (· * 10)
  assert! (← ref.get) == 10

#eval do (← racerAll.toRawEIO).wait
