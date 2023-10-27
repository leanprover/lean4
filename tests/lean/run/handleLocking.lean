/-!
This test covers the file handle locking functionality in `IO`.
-/

def testFile := "handleLocking.lock"

/-- Test an exclusive lock. -/
def test1 : IO Unit := do
  let h1 ← IO.FS.Handle.mk testFile .write
  h1.lock
  let h2 ← IO.FS.Handle.mk testFile .write
  if (← h2.tryLock) then
    throw <| IO.userError "incorrectly acquired 2 exclusive locks"
  if (← h2.tryLock (exclusive := false)) then
    throw <| IO.userError "incorrectly acquired an exclusive and shared lock"
  h1.unlock
  unless (← h2.tryLock) do
    throw <| IO.userError "failed to unlock exclusive lock and then lock"

#eval test1

/-- Test unlock on handle free (and thus a close). -/
def test2 : IO Unit := do
  let h ← IO.FS.Handle.mk testFile .write
  h.lock
  let h ← IO.FS.Handle.mk testFile .write -- expected to free old `h`
  unless (← h.tryLock) do
    throw <| IO.userError "handle free failed to unlock"

#eval test2

/-- Test shared locks. -/
def test3 : IO Unit := do
  let h1 ← IO.FS.Handle.mk testFile .write
  h1.lock (exclusive := false)
  let h2 ← IO.FS.Handle.mk testFile .write
  if (← h2.tryLock) then
    throw <| IO.userError "incorrectly acquired a shared and exclusive lock"
  unless (← h2.tryLock (exclusive := false)) do
    throw <| IO.userError "failed to acquire 2 shared locks"
  h1.unlock
  h2.unlock
  unless (← h2.tryLock) do
    throw <| IO.userError "failed to unlock shared locks and then lock"

#eval test3
