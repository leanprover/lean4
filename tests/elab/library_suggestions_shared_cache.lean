module

import all Lean.LibrarySuggestions.SymbolFrequency

/-!
Library suggestions cache their imported indexes in `SharedCache`s. Concurrent callers must share
one computation. A computation that fails or is interrupted must not be cached, and the callers
waiting for it must compute the value themselves. A cancelled caller must stop waiting without
cancelling the computation. Run with `-j1` to check that blocked callers let queued work proceed.
-/

open Lean LibrarySuggestions

/-- Run `x` in the worker pool, with `tk?` as its cancellation token. -/
def spawn (x : CoreM α) (tk? : Option IO.CancelToken := none) :
    CoreM (Task (Except Exception α)) := do
  let act ← Core.wrapAsync (fun (_ : Unit) => x) tk?
  EIO.asTask (act ())

/-- A computation that signals `started` and then blocks until `release` is resolved. -/
def blocking (started release : IO.Promise Unit) (x : CoreM α) : CoreM α := do
  started.resolve ()
  IO.wait release.result!
  x

def isOk : Except Exception α → Bool
  | .ok _ => true
  | .error _ => false

-- Concurrent callers share one computation.
run_meta do
  let cache : SharedCache Nat ← IO.mkRef none
  let runs ← IO.mkRef 0
  let started ← IO.Promise.new
  let release ← IO.Promise.new
  let compute := blocking started release do runs.modify (· + 1); return 42
  let first ← spawn (cache.getOrCompute compute)
  IO.wait started.result!
  let others ← (List.range 4).mapM fun _ => spawn (cache.getOrCompute compute)
  IO.sleep 50
  release.resolve ()
  for t in first :: others do
    let .ok 42 ← IO.wait t | throwError "expected 42"
  assert! (← runs.get) == 1
  assert! (← cache.getOrCompute (throwError "cached value expected")) == 42

-- A failed computation is not cached, and a waiting caller computes the value itself.
run_meta do
  let cache : SharedCache Nat ← IO.mkRef none
  let started ← IO.Promise.new
  let release ← IO.Promise.new
  let first ← spawn (cache.getOrCompute (blocking started release (throwError "failed")))
  IO.wait started.result!
  let second ← spawn (cache.getOrCompute (pure 7))
  IO.sleep 50
  release.resolve ()
  let .error e ← IO.wait first | throwError "expected the first computation to fail"
  assert! !e.isInterrupt
  let .ok 7 ← IO.wait second | throwError "expected 7"
  assert! (← cache.getOrCompute (pure 8)) == 7

-- An interrupted computation is not cached, and a caller that was not cancelled computes the value
-- itself.
run_meta do
  let cache : SharedCache Nat ← IO.mkRef none
  let started ← IO.Promise.new
  let release ← IO.Promise.new
  let tk ← IO.CancelToken.new
  let compute := blocking started release do Core.checkInterrupted; return 0
  let first ← spawn (cache.getOrCompute compute) tk
  IO.wait started.result!
  let second ← spawn (cache.getOrCompute (pure 7))
  IO.sleep 50
  tk.set
  release.resolve ()
  let .error e ← IO.wait first | throwError "expected the first computation to be interrupted"
  assert! e.isInterrupt
  let .ok 7 ← IO.wait second | throwError "expected 7"
  assert! (← cache.getOrCompute (pure 8)) == 7

-- A cancelled caller stops waiting while the computation continues, and the result is cached.
run_meta do
  let cache : SharedCache Nat ← IO.mkRef none
  let started ← IO.Promise.new
  let release ← IO.Promise.new
  let first ← spawn (cache.getOrCompute (blocking started release (pure 42)))
  IO.wait started.result!
  let tk ← IO.CancelToken.new
  let waiter ← spawn (cache.getOrCompute (pure 0)) tk
  IO.sleep 50
  tk.set
  -- `first` is still blocked, so `waiter` must return on its own.
  let .error e ← IO.wait waiter | throwError "expected the waiter to be interrupted"
  assert! e.isInterrupt
  assert! !(← IO.hasFinished first)
  release.resolve ()
  let .ok 42 ← IO.wait first | throwError "expected 42"
  assert! (← cache.getOrCompute (pure 0)) == 42

-- Concurrent first uses of the symbol frequency map get the same map object, computed once.
unsafe def sameObject (a b : NameMap Nat) : Bool := ptrAddrUnsafe a == ptrAddrUnsafe b

run_meta do
  assert! (← importedRelevantConstantsRef.get).isNone
  let tk ← IO.CancelToken.new
  let tasks ← (List.range 4).mapM fun _ => spawn symbolFrequencyMap tk
  let maps ← tasks.mapM fun t => do
    let .ok map ← IO.wait t | throwError "expected the symbol frequency map"
    return map
  let map := maps.head!
  assert! map.getD `Nat 0 > 0
  assert! maps.all (unsafe sameObject map ·)
