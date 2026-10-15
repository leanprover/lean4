import Std.Internal.UV.System

/-!
`osGetenv` must not find a variable for a name that contains `=`: no variable can have such a name,
and `osSetenv` rejects it. The C library's `getenv` matches only up to the `=` on macOS, so
`osGetenv "PATH=junk"` returns the value of `PATH` (found while testing PR #15653; this predates it).
-/

open Std.Internal.UV

#eval do
  if System.Platform.isWindows then
    return
  System.osSetenv "LEAN_UV_EQ_NAME" "value"
  for name in ["LEAN_UV_EQ_NAME=junk", "LEAN_UV_EQ_NAME=", "LEAN_UV_EQ_NAME=value"] do
    if let some v ← System.osGetenv name then
      throw <| IO.userError s!"getenv {name} returned {v}"
  System.osUnsetenv "LEAN_UV_EQ_NAME"
