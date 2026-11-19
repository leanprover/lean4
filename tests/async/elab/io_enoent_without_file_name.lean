import Std.Internal.UV

/-!
Operations that fail with "no such file or directory" but have no file name to report throw
`IO.Error.noFileOrDirectory` instead of crashing: querying a deleted working directory, and creating
a temporary file or directory under a nonexistent `TMPDIR`.
-/

open Std.Internal.UV

def expectNoFile (what : String) (act : IO α) : IO Unit := do
  match ← act.toBaseIO with
  | .error (.noFileOrDirectory ..) => pure ()
  | .error e => throw <| IO.userError s!"{what}: unexpected error: {e}"
  | .ok _ => throw <| IO.userError s!"{what}: succeeded"

#eval show IO Unit from do
  if _root_.System.Platform.isWindows then return
  let orig ← System.cwd
  let dir ← IO.FS.createTempDir
  try
    System.chdir dir.toString
    IO.FS.removeDir dir
    expectNoFile "System.cwd" System.cwd
    expectNoFile "IO.Process.getCurrentDir" IO.Process.getCurrentDir
  finally
    System.chdir orig

#eval show IO Unit from do
  if _root_.System.Platform.isWindows then return
  let tmp? ← System.osGetenv "TMPDIR"
  try
    System.osSetenv "TMPDIR" "/nonexistent-lean-test-dir"
    expectNoFile "IO.FS.createTempFile" IO.FS.createTempFile
    expectNoFile "IO.FS.createTempDir" IO.FS.createTempDir
  finally
    match tmp? with
    | some t => System.osSetenv "TMPDIR" t
    | none => System.osUnsetenv "TMPDIR"
