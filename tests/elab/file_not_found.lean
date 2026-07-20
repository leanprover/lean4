prelude
import Init.System.IO

/-!
Tests the messages of file-system `IO` errors. The numeric error codes in these messages are
platform-specific (e.g. they differ between POSIX and Windows), so `#guard_msgs` substring
matching is used to check the descriptive text without the error code. Since the error code
precedes the reported file name and error details, those are checked by separate substring
matches.
-/

def nonexistent_file := "file_not_found.lean.nonexistent.txt"
def readonly_file := "file_not_found.lean.readonly.txt"

open IO.FS

def usingIO {α} (x : IO α) : IO α := x

/-- error: no such file or directory -/
#guard_msgs (substring := true) in
#eval (discard $ IO.FS.Handle.mk nonexistent_file Mode.read : IO Unit)

/-- file: file_not_found.lean.nonexistent.txt -/
#guard_msgs (substring := true) in
#eval (discard $ IO.FS.Handle.mk nonexistent_file Mode.read : IO Unit)

#guard_msgs in
#eval usingIO do
  if (← System.FilePath.pathExists readonly_file) then pure ()
  else
    IO.FS.withFile readonly_file Mode.write $ fun _ => pure ()
  IO.setAccessRights readonly_file { user := { read := true } };
  pure ()

/-- error: permission denied -/
#guard_msgs (substring := true) in
#eval (discard $ IO.FS.Handle.mk readonly_file Mode.write : IO Unit)

/-- file: file_not_found.lean.readonly.txt -/
#guard_msgs (substring := true) in
#eval (discard $ IO.FS.Handle.mk readonly_file Mode.write : IO Unit)

/-- error: invalid argument -/
#guard_msgs (substring := true) in
#eval usingIO do
  let h ← IO.FS.Handle.mk readonly_file Mode.read;
  h.putStr "foo";
  IO.println "foo";
  pure ()

/-- bad file descriptor -/
#guard_msgs (substring := true) in
#eval usingIO do
  let h ← IO.FS.Handle.mk readonly_file Mode.read;
  h.putStr "foo";
  IO.println "foo";
  pure ()
