import Std.Internal.UV.System

/-!
The `lean` binary never calls `uv_setup_args`, so libuv reports `ENOBUFS` from `getProcessTitle` for
every buffer size. The call must fail with that error rather than grow its buffer until an allocation
fails with `ENOMEM` (or, under ASan, aborts the process).
-/

open Std.Internal.UV

#eval show IO Unit from do
  -- On Windows libuv reads the console title, which needs no `uv_setup_args`.
  if System.Platform.isWindows then
    return
  match ← System.getProcessTitle.toBaseIO with
  -- `ENOBUFS` and `ENOMEM` both decode to `resourceExhausted`, so the libuv message tells them apart.
  | .error (.resourceExhausted _ _ details) =>
    unless details == "no buffer space available" do
      throw <| IO.userError s!"getProcessTitle: {details}"
  | .error e => throw <| IO.userError s!"getProcessTitle: unexpected error {e}"
  | .ok t => throw <| IO.userError s!"getProcessTitle: read {t.length} bytes without uv_setup_args"
