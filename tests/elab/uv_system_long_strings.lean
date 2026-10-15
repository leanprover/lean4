import Std.Internal.UV

/-!
`System.osHomedir` and `System.osTmpdir` return values longer than `PATH_MAX` instead of failing
with `ENOBUFS`. Both read an environment variable first, which the test sets to a long path.
-/

open Std.Internal.UV

#eval show IO Unit from do
  if _root_.System.Platform.isWindows then return
  let long := "/" ++ String.ofList (List.replicate 5000 'a')
  let home? ← System.osGetenv "HOME"
  let tmp? ← System.osGetenv "TMPDIR"
  try
    System.osSetenv "HOME" long
    System.osSetenv "TMPDIR" long
    let home ← System.osHomedir
    let tmp ← System.osTmpdir
    unless home == long do
      throw <| IO.userError s!"osHomedir returned a string of length {home.length}"
    unless tmp == long do
      throw <| IO.userError s!"osTmpdir returned a string of length {tmp.length}"
  finally
    match home? with
    | some h => System.osSetenv "HOME" h
    | none => System.osUnsetenv "HOME"
    match tmp? with
    | some t => System.osSetenv "TMPDIR" t
    | none => System.osUnsetenv "TMPDIR"
