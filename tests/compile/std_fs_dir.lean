import Std.FS
import Std.Path.Notation

/-!
Checks that the `Std.FS.Dir` FFI bindings link into a compiled binary, not just the interpreter.
-/

open Std Std.FS

def main : IO Unit :=
  withTempDir fun root => do
    createDirAll (root / path("a") / path("b"))
    writeFile (root / path("a") / path("b") / path("deep.txt")) "deep"

    -- Entries arrive in filesystem order, so sort before printing.
    let mut entries := #[]
    for entry in ← walk root do
      entries := entries.push s!"{entry.fileName} {← entry.isDir}"
    for entry in entries.qsort (· < ·) do
      IO.println entry
