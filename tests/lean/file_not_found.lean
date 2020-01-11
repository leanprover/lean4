prelude
import Init.System.IO

open IO.FS

#eval (IO.FS.Handle.mk "non-existent-file.txt" Mode.read *> pure () : IO Unit)
#eval do condM (IO.fileExists "readonly.txt")
               (pure ())
               (IO.FS.withFile "readonly.txt" Mode.write $ fun _ => pure ());
         IO.setAccessRights "readonly.txt" { user := { read := true } };
         (pure () : IO Unit)
#eval (IO.FS.Handle.mk "readonly.txt" Mode.write *> pure () : IO Unit)
#eval do h ← IO.FS.Handle.mk "readonly.txt" Mode.read;
         h.putStr "foo";
         IO.println "foo";
         (pure () : IO Unit)
