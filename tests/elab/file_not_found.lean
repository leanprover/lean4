/-!
Tests that `errno` values from file operations are decoded into the correct `IO.Error`
constructor and parameters. The `osCode` parameter is not compared because it is
platform-specific.
-/

deriving instance BEq, Repr for IO.Error

/-- Replaces the platform-specific `osCode` with `0`. -/
def scrubOsCode : IO.Error → IO.Error
  | .alreadyExists fn _ d       => .alreadyExists fn 0 d
  | .otherError _ d             => .otherError 0 d
  | .resourceBusy _ d           => .resourceBusy 0 d
  | .resourceVanished _ d       => .resourceVanished 0 d
  | .unsupportedOperation _ d   => .unsupportedOperation 0 d
  | .hardwareFault _ d          => .hardwareFault 0 d
  | .unsatisfiedConstraints _ d => .unsatisfiedConstraints 0 d
  | .illegalOperation _ d       => .illegalOperation 0 d
  | .protocolError _ d          => .protocolError 0 d
  | .timeExpired _ d            => .timeExpired 0 d
  | .interrupted fn _ d         => .interrupted fn 0 d
  | .noFileOrDirectory fn _ d   => .noFileOrDirectory fn 0 d
  | .invalidArgument fn _ d     => .invalidArgument fn 0 d
  | .permissionDenied fn _ d    => .permissionDenied fn 0 d
  | .resourceExhausted fn _ d   => .resourceExhausted fn 0 d
  | .inappropriateType fn _ d   => .inappropriateType fn 0 d
  | .noSuchThing fn _ d         => .noSuchThing fn 0 d
  | e                           => e

/-- Asserts that `x` fails with `expected`, ignoring the error's `osCode` (`expected` should use
`0` in its place). -/
def assertError (x : IO Unit) (expected : IO.Error) : IO Unit := do
  match ← x.toBaseIO with
  | .ok _ => throw <| IO.userError "expected an error, but the action succeeded"
  | .error e =>
    let actual := scrubOsCode e
    unless actual == expected do
      throw <| IO.userError s!"expected error: {repr expected}\nactual error:   {repr actual}"

def nonexistentFile := "file_not_found.lean.nonexistent.txt"
def readonlyFile := "file_not_found.lean.readonly.txt"

#guard_msgs in
#eval assertError (discard <| IO.FS.Handle.mk nonexistentFile .read)
  (.noFileOrDirectory nonexistentFile 0 "no such file or directory")

#guard_msgs in
#eval show IO Unit from do
  IO.FS.withFile readonlyFile .write fun _ => pure ()
  IO.setAccessRights readonlyFile { user := { read := true } }

#guard_msgs in
#eval assertError (discard <| IO.FS.Handle.mk readonlyFile .write)
  (.permissionDenied (some readonlyFile) 0 "permission denied")

#guard_msgs in
#eval assertError
  (do
    let h ← IO.FS.Handle.mk readonlyFile .read
    h.putStr "foo")
  (.invalidArgument none 0 "bad file descriptor")
