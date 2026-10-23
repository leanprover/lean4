import Std.Internal.UV.System

/-!
`osGetenv` must not find a variable for a name with an `=` past its first character: no variable
has such a name, and `osSetenv` rejects it, but on macOS the C library's `getenv` matches only up to
the `=`, so `osGetenv "PATH=junk"` would return the value of `PATH`. A leading `=` belongs to the
name, as in the hidden `=C:` variables of Windows, so every variable `osEnviron` lists is found by
its name.
-/

open Std.Internal.UV

#eval show IO Unit from do
  for (name, value) in ← System.osEnviron do
    let found ← System.osGetenv name
    unless found == some value do
      throw <| IO.userError s!"getenv {name} returned {found}, but environ lists {value}"

#eval show IO Unit from do
  if System.Platform.isWindows then
    return
  System.osSetenv "LEAN_UV_EQ_NAME" "value"
  try
    for name in ["LEAN_UV_EQ_NAME=junk", "LEAN_UV_EQ_NAME=", "LEAN_UV_EQ_NAME=value"] do
      if let some v ← System.osGetenv name then
        throw <| IO.userError s!"getenv {name} returned {v}"
  finally
    System.osUnsetenv "LEAN_UV_EQ_NAME"
