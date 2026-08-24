/-!
Blocks until `slowA`'s marker appears (path in `FAILFAST_SYNC`). Under
`--fail-fast` the marker is written only once cancellation is active, so
`SlowChain.B`'s compile continuation deterministically observes a set token.
Bounded, in case the marker never appears.
-/
#eval show IO Unit from do
  let some path ← IO.getEnv "FAILFAST_SYNC"
    | throw <| IO.userError "FAILFAST_SYNC not set"
  for _ in [0:100] do
    if ← System.FilePath.pathExists ⟨path⟩ then break
    IO.sleep 100
