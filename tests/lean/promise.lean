open IO

-- not in the run/ directory because then it would be run with -j0

#eval do
  let promise ← Promise.new
  promise.resolve 42
  assert! promise.result.get = 42

#eval do
  let ch ← Channel.new

  let out ← IO.mkRef #[]
  ch.send 0
  let drainFinished ← ch.forAsync fun x => out.modify (·.push x)
  ch.send 1
  ch.close
  ch.send 2

  IO.wait drainFinished
  assert! (← out.get) = #[0, 1]
