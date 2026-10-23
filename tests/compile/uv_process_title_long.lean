import Std.Internal.UV.System

/-!
`getProcessTitle` returns a title of 512 bytes or more instead of failing with `ENOBUFS`. libuv keeps
the title in the memory of the original command line, so the test is run with a 2000-byte argument
to leave room for the longest title, which must then be read back whole.
-/

open Std.Internal.UV

def main (args : List String) : IO Unit := do
  unless (args.headD "").length ≥ 2000 do
    throw <| IO.userError "expected a 2000-byte argument to make room for the title"
  for n in [100, 511, 512, 1000] do
    let title := String.ofList (List.replicate n 'T')
    System.setProcessTitle title
    match ← System.getProcessTitle.toBaseIO with
    | .ok t =>
      unless t == title do
        throw <| IO.userError s!"title of {n} bytes read back as {t.length} bytes"
    | .error e => throw <| IO.userError s!"title of {n} bytes: {e}"
  IO.println "ok"
