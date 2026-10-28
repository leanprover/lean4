import Std.Internal.UV.System

/-!
The `lean` binary never calls `uv_setup_args`, so on Linux and macOS libuv has no memory to keep the
process title in and reports `ENOBUFS` from `getProcessTitle` for every buffer size. The call fails
with that error after a bounded number of retries with larger buffers, and `setProcessTitle` fails
with it too.
-/

open Std.Internal.UV

def expectNoBuffers (what : String) (x : IO α) : IO Unit := do
  match ← x.toBaseIO with
  -- `ENOBUFS` and `ENOMEM` both decode to `resourceExhausted`, so the libuv message tells them
  -- apart.
  | .error (.resourceExhausted _ _ details) =>
    unless details == "no buffer space available" do
      throw <| IO.userError s!"{what}: {details}"
  | .error e => throw <| IO.userError s!"{what}: unexpected error {e}"
  | .ok _ => throw <| IO.userError s!"{what}: succeeded without uv_setup_args"

#eval show IO Unit from do
  -- Windows and the BSDs keep their own copy of the title, which needs no `uv_setup_args`.
  unless System.Platform.isLinux || System.Platform.isOSX do
    return
  expectNoBuffers "getProcessTitle" System.getProcessTitle
  expectNoBuffers "setProcessTitle" (System.setProcessTitle "title")
