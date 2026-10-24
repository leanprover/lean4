import Std.Internal.UV.System

/-!
Edge cases of the environment and path queries that cross the libuv FFI (PR #15653): an empty value
is distinct from an unset variable, values containing `=` or non-ASCII text round-trip, values around
the 1024-byte stack buffer of `osGetenv` (including a multi-byte character straddling it) and a 1 MB
value come back whole, and names or values with an embedded NUL are rejected instead of being
truncated at the NUL. `cwd` is checked at exactly `PATH_MAX` bytes on macOS, the one length at which
libuv asks for a larger buffer.
-/

open Std.Internal.UV

def check (name : String) (cond : Bool) (detail : String := "") : IO Unit :=
  unless cond do
    throw <| IO.userError s!"{name}: {detail}"

def expectInvalidArgument (what : String) (x : IO α) : IO Unit := do
  match ← x.toBaseIO with
  | .error (.invalidArgument ..) => pure ()
  | .error e => throw <| IO.userError s!"{what}: unexpected error {e}"
  | .ok _ => throw <| IO.userError s!"{what}: succeeded"

#eval do
  if System.Platform.isWindows then
    return
  System.osSetenv "LEAN_UV_ENV_EMPTY" ""
  check "empty value" ((← System.osGetenv "LEAN_UV_ENV_EMPTY") == some "")
  check "empty value in environ"
    ((← System.osEnviron).any (· == ("LEAN_UV_ENV_EMPTY", "")))
  System.osUnsetenv "LEAN_UV_ENV_EMPTY"
  check "unset" ((← System.osGetenv "LEAN_UV_ENV_EMPTY") == none)

  System.osSetenv "LEAN_UV_ENV_EQ" "a=b=c"
  check "value with =" ((← System.osGetenv "LEAN_UV_ENV_EQ") == some "a=b=c")
  System.osSetenv "LEAN_UV_ENV_UNICODE" "héllo→✓𝔸"
  check "unicode value" ((← System.osGetenv "LEAN_UV_ENV_UNICODE") == some "héllo→✓𝔸")

  for n in [1023, 1024, 1025, 1000000] do
    let v := String.ofList (List.replicate n 'x')
    System.osSetenv "LEAN_UV_ENV_BIG" v
    let r ← System.osGetenv "LEAN_UV_ENV_BIG"
    check s!"value of {n} bytes" (r == some v) s!"{r.map String.length}"
  let straddle := String.ofList (List.replicate 1022 'x') ++ "✓✓"
  System.osSetenv "LEAN_UV_ENV_BIG" straddle
  check "multi-byte value across the buffer size" ((← System.osGetenv "LEAN_UV_ENV_BIG") == some straddle)
  System.osUnsetenv "LEAN_UV_ENV_BIG"

  -- Names and values are C strings: a NUL would silently cut them short.
  expectInvalidArgument "setenv NUL in name" <| System.osSetenv "LEAN_UV_ENV\x00X" "v"
  expectInvalidArgument "setenv NUL in value" <| System.osSetenv "LEAN_UV_ENV_NUL" "v\x00w"
  check "NUL value not stored" ((← System.osGetenv "LEAN_UV_ENV_NUL") == none)
  expectInvalidArgument "unsetenv NUL in name" <| System.osUnsetenv "PATH\x00X"
  check "unsetenv with NUL left PATH alone" ((← System.osGetenv "PATH").isSome)
  check "getenv NUL in name" ((← System.osGetenv "PATH\x00X") == none)
  expectInvalidArgument "setenv empty name" <| System.osSetenv "" "v"
  expectInvalidArgument "setenv = in name" <| System.osSetenv "LEAN_UV=X" "v"
  expectInvalidArgument "chdir NUL" <| System.chdir "/\x00tmp"
  expectInvalidArgument "setProcessTitle NUL" <| System.setProcessTitle "a\x00b"

-- `PATH_MAX` is 1024 on macOS. libuv reads the working directory into the 1024-byte stack buffer when
-- it fits and reports the size it needs when it is exactly 1024 bytes long.
#eval do
  unless System.Platform.isOSX do
    return
  let base ← System.cwd
  let root := s!"{← System.osTmpdir}/lean-uv-cwd-{← System.osGetPid}"
  IO.FS.createDirAll root
  try
    for target in [1023, 1024] do
      System.chdir root
      IO.FS.createDir s!"t{target}"
      System.chdir s!"t{target}"
      -- The real path: on macOS the temporary directory is behind the `/var` symlink.
      let mut cur ← System.cwd
      while cur.length < target do
        -- Each component adds `n + 1` bytes; never leave a remainder of 1, which has no component.
        let r := target - cur.length
        let n := if r ≤ 201 then r - 1 else if r == 202 then 198 else 200
        let comp := String.ofList (List.replicate n 'd')
        IO.FS.createDir comp
        System.chdir comp
        cur := cur ++ "/" ++ comp
      let c ← System.cwd
      check s!"cwd of {target} bytes" (c == cur && c.utf8ByteSize == target) s!"got {c.length} bytes"
  finally
    System.chdir base
    IO.FS.removeDirAll root
