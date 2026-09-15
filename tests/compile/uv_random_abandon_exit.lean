import Std.Internal.UV

/-!
Returning from `main` while threadpool workers are still writing large `uv_random` buffers must not
crash; see `uv_random_exit`. Each `ByteArray` has to stay alive while its worker writes into it.
-/

open Std.Internal.UV

def main : IO Unit := do
  for _ in [0:4] do
    discard <| System.random (64 * 1024 * 1024)
  IO.println "exiting"
