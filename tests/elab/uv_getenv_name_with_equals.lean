import Std.Internal.UV.System

/-!
`osGetenv` must not find a variable for a name with an `=` past its first character: no variable
has such a name, and `osSetenv` rejects it, but on macOS the C library's `getenv` matches only up to
the `=`, so `osGetenv "PATH=junk"` would return the value of `PATH`. On Windows a leading `=`
belongs to the name, as in the hidden `=C:` variables, so every variable `osEnviron` lists is found
by its name. Elsewhere a name that starts with `=`, or is empty, is not found either: macOS
`getenv` would match it to any variable whose name starts with `=`. `setenv` cannot create such a
variable, so Python's `execve` plants one in a child `lean` process that runs those lookups.
-/

open Std.Internal.UV

#eval show IO Unit from do
  for (name, value) in ← System.osEnviron do
    let found ← System.osGetenv name
    unless found == some value do
      throw <| IO.userError s!"getenv {name} returned {found}, but environ lists {value}"

-- Windows accepts an `=` as the first character of a name, so the test sets such a variable itself
-- rather than rely on the environment it is run in.
#eval show IO Unit from do
  unless System.Platform.isWindows do
    return
  System.osSetenv "=LEAN_UV_EQ_LEAD" "value"
  try
    let found ← System.osGetenv "=LEAN_UV_EQ_LEAD"
    unless found == some "value" do
      throw <| IO.userError s!"getenv =LEAN_UV_EQ_LEAD returned {found}"
    unless (← System.osEnviron).any (· == ("=LEAN_UV_EQ_LEAD", "value")) do
      throw <| IO.userError "environ does not list =LEAN_UV_EQ_LEAD"
  finally
    System.osUnsetenv "=LEAN_UV_EQ_LEAD"

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

def childSource : String := r#"
import Std.Internal.UV.System
open Std.Internal.UV

#eval show IO Unit from do
  -- libuv splits a Unix environment entry at its first `=`.
  unless (← System.osEnviron).any (· == ("", "LEAN_UV_EQ_HIDDEN=secret")) do
    IO.println "=LEAN_UV_EQ_HIDDEN was not planted"
  for name in ["", "=", "=C:", "=HOME", "=LEAN_UV_EQ_HIDDEN"] do
    if let some v ← System.osGetenv name then
      IO.println s!"osGetenv {repr name} returned {repr v}"
"#

def plant : String :=
  "import os, sys; env = dict(os.environ); env['=LEAN_UV_EQ_HIDDEN'] = 'secret'; " ++
  "os.execve(sys.argv[1], sys.argv[1:], env)"

#eval show IO Unit from do
  if System.Platform.isWindows then
    return
  IO.FS.withTempDir fun dir => do
    let child := dir / "child.lean"
    IO.FS.writeFile child childSource
    let out ← IO.Process.output {
      cmd := "python3"
      args := #["-I", "-c", plant, (← IO.appPath).toString, child.toString]
    }
    unless out.exitCode == 0 && out.stdout.isEmpty do
      throw <| IO.userError s!"child exited with {out.exitCode}:\n{out.stdout}{out.stderr}"
