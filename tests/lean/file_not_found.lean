prelude
import Init.System.IO

open IO.FS
def usingIO {α} (x : IO α) : IO α := x
#eval (discard $ IO.FS.Handle.mk "non-existent-file.txt" Mode.read : IO Unit)
#eval usingIO do
  if (← System.FilePath.pathExists "readonly.txt") then pure ()
  else
    IO.FS.withFile "readonly.txt" Mode.write $ fun _ => pure ()
  IO.setAccessRights "readonly.txt" { user := { read := true } };
  pure ()
#eval (discard $ IO.FS.Handle.mk "readonly.txt" Mode.write : IO Unit)
#eval usingIO do
  let h ← IO.FS.Handle.mk "readonly.txt" Mode.read;
  h.putStr "foo";
  IO.println "foo";
  pure ()
