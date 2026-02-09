import Std.Sync.Channel

open IO

-- not in the run/ directory because then it would be run with -j0

#eval do
  let promise ← Promise.new
  promise.resolve 42
  assert! promise.result?.get = some 42


/- Dropping a promise resolves `result?` to `none`. -/
#eval do
  let promise : Promise Nat ← Promise.new
  assert! promise.result?.get = none

#eval show IO _ from do
  let ch ← Std.CloseableChannel.new

  let out ← IO.mkRef #[]
  ch.sync.send 0
  let drainFinished ← ch.forAsync fun x => out.modify (·.push x)
  ch.sync.send 1
  ch.close
  assert! (← EIO.toBaseIO (ch.sync.send 2)) matches .error .closed

  IO.wait drainFinished
  assert! (← out.get) = #[0, 1]
