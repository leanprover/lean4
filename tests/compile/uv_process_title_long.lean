import Std.Internal.UV.System

/-!
`getProcessTitle` returns a title of 512 bytes or more instead of failing with `ENOBUFS`. libuv keeps
the title in the memory of the original command line, so the test is run with a 2000-byte argument
to leave room for a long title; the title read back is the one set, cut to that room if needed.
Found while testing PR #15653; the fixed 512-byte buffer predates it.
-/

open Std.Internal.UV

def main (args : List String) : IO Unit := do
  for n in [100, 511, 512, 1000] do
    let title := String.ofList (List.replicate n 'T')
    System.setProcessTitle title
    match ← System.getProcessTitle.toBaseIO with
    | .ok t =>
      unless title.startsWith t && (args.headD "").length ≥ 2000 && t.length == n do
        throw <| IO.userError s!"title of {n} bytes read back as {t.length} bytes"
    | .error e => throw <| IO.userError s!"title of {n} bytes: {e}"
  IO.println "ok"
