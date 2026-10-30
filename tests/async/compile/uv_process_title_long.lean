import Std.Internal.UV.System

/-!
`getProcessTitle` returns a title of 512 bytes or more instead of failing with `ENOBUFS`. On Linux
and macOS libuv keeps the title in the memory of the original command line, so the test is run with
a 2000-byte argument to leave room for titles of up to 1000 bytes, which must be read back whole. A
5000-byte title does not fit there and must be read back cut to a prefix of at least 2000 bytes;
elsewhere libuv keeps its own copy, which holds it whole.
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
  let long := String.ofList (List.replicate 5000 'T')
  System.setProcessTitle long
  let t ← System.getProcessTitle
  if System.Platform.isLinux || System.Platform.isOSX then
    unless long.startsWith t && 2000 ≤ t.utf8ByteSize && t.utf8ByteSize < 5000 do
      throw <| IO.userError s!"title of 5000 bytes read back as {t.utf8ByteSize} bytes, uncut"
  else
    unless t == long do
      throw <| IO.userError s!"title of 5000 bytes read back as {t.utf8ByteSize} bytes"
  IO.println "ok"
