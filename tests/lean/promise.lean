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

#eval do
  let ch ← Std.Channel.new

  let out ← IO.mkRef #[]
  ch.send 0
  let drainFinished ← ch.forAsync fun x => out.modify (·.push x)
  ch.send 1
  ch.close
  ch.send 2

  IO.wait drainFinished
  assert! (← out.get) = #[0, 1]
