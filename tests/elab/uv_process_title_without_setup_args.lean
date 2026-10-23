import Std.Internal.UV.System

/-!
The `lean` binary never calls `uv_setup_args`, so libuv reports `ENOBUFS` from `getProcessTitle` for
every buffer size. The call must fail with that error rather than grow its buffer until an allocation
fails with `ENOMEM` (or, under ASan, aborts the process).
-/

open Std.Internal.UV

#eval show IO Unit from do
  if System.Platform.isWindows then
    return
  match ← System.getProcessTitle.toBaseIO with
  | .error (.resourceExhausted _ code _) =>
    -- `ENOMEM` is 12 on Linux and macOS.
    if code == 12 then
      throw <| IO.userError "getProcessTitle: out of memory"
  | .error e => throw <| IO.userError s!"getProcessTitle: unexpected error {e}"
  | .ok t => throw <| IO.userError s!"getProcessTitle: read {t.length} bytes without uv_setup_args"
