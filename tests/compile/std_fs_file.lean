import Std.FS

/-!
Checks that the `Std.FS.File` FFI bindings link into a compiled binary, not just the interpreter.
-/

open Std Std.FS

def main : IO Unit :=
  withTempFile fun file path => do
    file.putStrLn "hello"
    file.syncAll
    IO.println (← readFile path)
    IO.println (← metadata path).byteSize
