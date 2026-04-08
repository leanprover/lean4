prelude
import Init.System.IO

def nonexistent_file := "file_not_found.lean.nonexistent.txt"
def readonly_file := "file_not_found.lean.readonly.txt"

open IO.FS
def usingIO {α} (x : IO α) : IO α := x
#eval (discard $ IO.FS.Handle.mk nonexistent_file Mode.read : IO Unit)
#eval usingIO do
  if (← System.FilePath.pathExists readonly_file) then pure ()
  else
    IO.FS.withFile readonly_file Mode.write $ fun _ => pure ()
  IO.setAccessRights readonly_file { user := { read := true } };
  pure ()
#eval (discard $ IO.FS.Handle.mk readonly_file Mode.write : IO Unit)
#eval usingIO do
  let h ← IO.FS.Handle.mk readonly_file Mode.read;
  h.putStr "foo";
  IO.println "foo";
  pure ()
